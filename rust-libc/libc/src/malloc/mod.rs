//! The memory allocator.
//!
//! # Design
//!
//! * Memory comes from 16 MiB aligned **segments** ([`segment`]) split
//!   into 256 KiB units; a **span** of one or four units serves one
//!   **size class** ([`classes`]). Allocations above 128 KiB get their own
//!   mapping. All metadata lives in the segment header, never next to
//!   user data.
//! * Every thread owns a [`Heap`] (embedded in its TCB) with, per size
//!   class, a list of spans that may have free blocks and a list of full
//!   spans. `malloc` and `free` on blocks owned by the calling thread
//!   touch no shared state and take no locks.
//! * Blocks freed by another thread are pushed on the span's lock-free
//!   `remote` stack and collected by the owner when it runs out of blocks.
//! * When a thread exits its spans are orphaned; any thread can adopt
//!   them later.
//!
//! # Hardening
//!
//! * Free blocks are linked through their first word, with the pointer
//!   XOR-encoded using a per-process random key and the slot address.
//!   Every pointer taken off a list is checked to be a block of the span.
//! * Each span has an allocation bitmap, so freeing a block twice, freeing
//!   an interior pointer or a pointer that was never allocated is detected
//!   and aborts the process.
//! * Metadata of released spans is poisoned, so a stale `free` into them
//!   is caught as well.
//! * Size computations use checked arithmetic (`calloc`, `reallocarray`).

pub mod classes;
pub mod segment;

use crate::errno::Errno;
use crate::sync::Mutex;
use classes::{CLASS_SIZE, MAX_SMALL, NUM_CLASSES, class_for, class_for_aligned};
use core::ffi::{c_int, c_void};
use core::ptr;
use core::sync::atomic::{AtomicUsize, Ordering};
use segment::{Owner, Span};

/// Per-process key for free list pointer encoding.
static KEY: AtomicUsize = AtomicUsize::new(0);

/// Seeds the pointer encoding key. Called once at startup.
pub fn init(random: [u8; 8]) {
    KEY.store(usize::from_ne_bytes(random) | 1, Ordering::Relaxed);
}

#[inline(always)]
fn key() -> usize {
    let k = KEY.load(Ordering::Relaxed);
    if k != 0 { k } else { 0x9e37_79b9_7f4a_7c15 }
}

/// Encodes a free list link stored at `slot`. Null encodes as 0 so an
/// empty list needs no key.
#[inline(always)]
fn encode(next: *mut u8, slot: usize) -> usize {
    if next.is_null() {
        0
    } else {
        next as usize ^ key() ^ slot.rotate_left(17)
    }
}

#[inline(always)]
fn decode(value: usize, slot: usize) -> *mut u8 {
    if value == 0 {
        ptr::null_mut()
    } else {
        (value ^ key() ^ slot.rotate_left(17)) as *mut u8
    }
}

/// Reports heap corruption and aborts (panics under test).
#[cold]
#[inline(never)]
fn corrupt(what: &str) -> ! {
    #[cfg(test)]
    {
        panic!("heap corruption: {what}");
    }
    #[cfg(not(test))]
    {
        let _ = crate::sys::write_all(2, b"rustlibc: heap corruption: ");
        let _ = crate::sys::write_all(2, what.as_bytes());
        let _ = crate::sys::write_all(2, b"\n");
        crate::exit::abort_now()
    }
}

/// Span size tiers (by unit count, see `classes::units_for_class`): an
/// empty span can serve any class of its tier.
const TIERS: usize = 3;

fn tier_of(class: usize) -> usize {
    match classes::units_for_class(class) {
        1 => 0,
        4 => 1,
        _ => 2,
    }
}

/// Bytes of empty spans a heap keeps for reuse before giving them back.
/// Returning a span (a TLB shootdown now, page faults later) is far
/// more expensive than holding on to it, and most programs' allocation
/// volume oscillates; this bounds the cost of a large drop in demand.
const RETAIN_MAX: usize = 64 << 20;

/// Retained spans idle for longer than this are given back whenever the
/// reserve is next touched.
const RETAIN_DECAY_MS: u64 = 250;

/// Most entries a per-class block cache holds.
const CACHE_MAX: usize = 32;

/// A cached block: the block itself and its allocation bit, so handing
/// it out is a store to the bit and nothing else. Blocks are 16-byte
/// aligned, so the bit's index within its bitmap byte rides in the low
/// bits of the pointer.
#[derive(Clone, Copy)]
#[repr(C)]
struct Entry {
    /// `ptr | bit`.
    tagged: usize,
    /// The bitmap byte holding the block's allocation bit.
    byte: *mut u8,
}

impl Entry {
    #[inline(always)]
    fn new(ptr: *mut u8, bitmap: *mut u64, idx: u32) -> Entry {
        Entry {
            tagged: ptr as usize | (idx as usize & 7),
            // SAFETY: the bitmap has a byte for every block.
            byte: unsafe { (bitmap as *mut u8).add(idx as usize / 8) },
        }
    }

    #[inline(always)]
    fn ptr(self) -> *mut u8 {
        (self.tagged & !0xf) as *mut u8
    }

    /// Marks the block allocated and returns it.
    ///
    /// # Safety
    /// The entry must be live (its span still owned by this thread).
    #[inline(always)]
    unsafe fn take(self) -> *mut u8 {
        // SAFETY: caller contract.
        unsafe { *self.byte |= 1 << (self.tagged & 7) };
        self.ptr()
    }

    /// The block's index in its span.
    fn index(self, bitmap: *mut u64) -> u32 {
        ((self.byte as usize - bitmap as usize) * 8 + (self.tagged & 7)) as u32
    }
}

/// Per-class cache of free blocks in front of the span machinery (the
/// idea of glibc's tcache and tcmalloc's per-thread caches), holding
/// blocks the span already counts as taken but whose allocation bit is
/// clear. `malloc` pops one and sets the bit; `free` clears the bit
/// after the usual validation and pushes. Refills and flushes move
/// several blocks at once, so the span's free list, bitmap and the
/// segment lookup are touched once per batch rather than per call. The
/// cache stores no metadata inside freed blocks, and a block freed twice
/// is still caught by its allocation bit.
#[repr(C)]
struct Cache {
    count: u8,
    cap: u8,
    /// Only `entries[..count]` are initialised (leaving the rest
    /// uninitialised keeps thread start-up from clearing the whole
    /// table).
    entries: [core::mem::MaybeUninit<Entry>; CACHE_MAX],
}

impl Cache {
    const EMPTY: Cache = Cache {
        count: 0,
        cap: 0,
        entries: [core::mem::MaybeUninit::uninit(); CACHE_MAX],
    };

    #[inline(always)]
    fn get(&self, i: usize) -> Entry {
        // SAFETY: callers only read entries below `count`.
        unsafe { self.entries[i].assume_init() }
    }

    #[inline(always)]
    fn set(&mut self, i: usize, e: Entry) {
        self.entries[i] = core::mem::MaybeUninit::new(e);
    }
}

/// Cache capacity for a class: 32 blocks for the small classes, fewer
/// as the blocks grow so that at most 64 KiB or so is cached per class
/// (one block for the big classes: enough for a free/malloc pair to
/// hit, without pinning megabytes per thread).
fn cache_cap(class: usize) -> u8 {
    ((64 * 1024) / CLASS_SIZE[class] as usize).clamp(1, CACHE_MAX) as u8
}

/// The span whose bitmap `word` belongs to (the word lies in the span's
/// first unit, and unit 0's header maps every unit to its span).
///
/// # Safety
/// `word` must be a bitmap word of a live span.
unsafe fn span_of_word(word: *mut u64) -> *mut Span {
    // SAFETY: caller contract.
    unsafe { segment::span_containing(word as *const u8) }
}

/// Frees of other threads' blocks waiting to be pushed on their spans'
/// remote stacks in batches (one CAS per span per batch instead of one
/// per block, the biggest cost of producer/consumer hand-offs).
const REMOTE_BUF: usize = 64;

#[derive(Clone, Copy)]
#[repr(C)]
struct RemoteEntry {
    ptr: *mut u8,
    span: *mut Span,
}

/// A thread's allocator state.
#[repr(C)]
pub struct Heap {
    /// The block caches (see [`Cache`]).
    cache: [Cache; NUM_CLASSES],
    /// Pending remote frees (see [`REMOTE_BUF`]).
    remote: [core::mem::MaybeUninit<RemoteEntry>; REMOTE_BUF],
    remote_count: u8,
    /// Spans that have (or may have, pending remote frees) free blocks.
    avail: [*mut Span; NUM_CLASSES],
    /// Spans with no locally free blocks.
    full: [*mut Span; NUM_CLASSES],
    /// Completely free spans kept for reuse, per tier: a doubly linked
    /// list, most recently freed first.
    empty: [*mut Span; TIERS],
    /// The other end of each `empty` list (the oldest span).
    empty_tail: [*mut Span; TIERS],
    /// Bytes held in `empty`.
    retained: usize,
    /// Cache refills and flushes, for the periodic reserve decay check.
    refills: u32,
}

impl Heap {
    /// An empty heap.
    pub const fn new() -> Self {
        Heap {
            cache: [Cache::EMPTY; NUM_CLASSES],
            remote: [core::mem::MaybeUninit::uninit(); REMOTE_BUF],
            remote_count: 0,
            avail: [ptr::null_mut(); NUM_CLASSES],
            full: [ptr::null_mut(); NUM_CLASSES],
            empty: [ptr::null_mut(); TIERS],
            empty_tail: [ptr::null_mut(); TIERS],
            retained: 0,
            refills: 0,
        }
    }

    #[inline(always)]
    fn id(&self) -> usize {
        self as *const Heap as usize
    }
}

impl Default for Heap {
    fn default() -> Self {
        Self::new()
    }
}

/// The calling thread's heap.
#[inline(always)]
fn current_heap() -> *mut Heap {
    // SAFETY: the TCB is valid for the life of the thread.
    unsafe { &raw mut (*crate::thread::current()).heap }
}

// ---------------------------------------------------------------------
// Intrusive doubly linked span lists.

/// Pushes `span` at the front of the list headed by `*head`.
///
/// # Safety
/// `span` must not be on any list.
unsafe fn list_push(head: *mut *mut Span, span: *mut Span) {
    // SAFETY: caller contract; all pointers are valid span metadata.
    unsafe {
        (*span).prev = ptr::null_mut();
        (*span).next = *head;
        if !(*head).is_null() {
            (**head).prev = span;
        }
        *head = span;
    }
}

/// Removes `span` from the list headed by `*head`.
///
/// # Safety
/// `span` must be on that list.
unsafe fn list_remove(head: *mut *mut Span, span: *mut Span) {
    // SAFETY: caller contract.
    unsafe {
        let (prev, next) = ((*span).prev, (*span).next);
        if prev.is_null() {
            *head = next;
        } else {
            (*prev).next = next;
        }
        if !next.is_null() {
            (*next).prev = prev;
        }
        (*span).prev = ptr::null_mut();
        (*span).next = ptr::null_mut();
    }
}

// ---------------------------------------------------------------------
// Span operations (owner only).

/// Takes a block from `span` like [`span_pop`], also saying whether the
/// block is known to be zero-filled (never used since its pages were
/// last cleared).
///
/// # Safety
/// The calling thread must own `span`.
#[inline]
unsafe fn span_pop_zeroed(span: *mut Span) -> (*mut u8, bool) {
    // SAFETY: caller contract.
    unsafe {
        let s = &mut *span;
        if s.free == 0 && s.bump < s.capacity {
            let zero = s.bump < s.zeroed;
            (span_pop(span), zero)
        } else {
            (span_pop(span), false)
        }
    }
}

/// Takes a block from `span`, or returns null if it has none.
///
/// # Safety
/// The calling thread must own `span`.
#[inline]
unsafe fn span_pop(span: *mut Span) -> *mut u8 {
    // SAFETY: caller contract.
    unsafe {
        let s = &mut *span;
        let p = if s.free != 0 {
            let p = decode(s.free, ptr::addr_of!(s.free) as usize);
            let Some(idx) = s.block_index(p) else {
                corrupt("free list pointer")
            };
            if s.is_allocated(idx) {
                corrupt("free list block is allocated");
            }
            let next = decode(*(p as *const usize), p as usize);
            s.free = encode(next, ptr::addr_of!(s.free) as usize);
            s.mark_allocated(idx);
            p
        } else if s.bump < s.capacity {
            let p = s.data.add(s.bump as usize * s.block_size as usize);
            s.mark_allocated(s.bump);
            s.bump += 1;
            p
        } else {
            return ptr::null_mut();
        };
        s.used += 1;
        p
    }
}

/// Takes a block from `span` for the cache: like [`span_pop`] but leaves
/// the allocation bit clear (a cached block is counted in `used` and has
/// its bit clear).
///
/// # Safety
/// The calling thread must own `span`.
#[inline]
unsafe fn span_pop_cached(span: *mut Span) -> Option<Entry> {
    // SAFETY: caller contract.
    unsafe {
        let s = &mut *span;
        let (p, idx) = if s.free != 0 {
            let p = decode(s.free, ptr::addr_of!(s.free) as usize);
            let Some(idx) = s.block_index(p) else {
                corrupt("free list pointer")
            };
            if s.is_allocated(idx) {
                corrupt("free list block is allocated");
            }
            let next = decode(*(p as *const usize), p as usize);
            s.free = encode(next, ptr::addr_of!(s.free) as usize);
            (p, idx)
        } else if s.bump < s.capacity {
            let idx = s.bump;
            s.bump += 1;
            (s.data.add(idx as usize * s.block_size as usize), idx)
        } else {
            return None;
        };
        s.used += 1;
        Some(Entry::new(p, s.bitmap, idx))
    }
}

/// Puts block `idx` (at `p`) back on `span`'s local free list.
///
/// # Safety
/// The calling thread must own `span`; `p` must be an allocated block.
#[inline]
unsafe fn span_push(span: *mut Span, p: *mut u8, idx: u32) {
    // SAFETY: caller contract.
    unsafe {
        let s = &mut *span;
        s.mark_free(idx);
        let head = decode(s.free, ptr::addr_of!(s.free) as usize);
        *(p as *mut usize) = encode(head, p as usize);
        s.free = encode(p, ptr::addr_of!(s.free) as usize);
        s.used -= 1;
    }
}

/// Like [`span_push`] for a block whose allocation bit is already clear
/// (it came from the cache).
///
/// # Safety
/// As for [`span_push`].
#[inline]
unsafe fn span_push_cached(span: *mut Span, p: *mut u8, idx: u32) {
    // SAFETY: caller contract.
    unsafe {
        let s = &mut *span;
        debug_assert!(!s.is_allocated(idx));
        let head = decode(s.free, ptr::addr_of!(s.free) as usize);
        *(p as *mut usize) = encode(head, p as usize);
        s.free = encode(p, ptr::addr_of!(s.free) as usize);
        s.used -= 1;
    }
}

/// Moves blocks freed by other threads onto the local free list.
/// Returns true if any were collected.
///
/// # Safety
/// The calling thread must own `span`.
unsafe fn span_collect_remote(span: *mut Span) -> bool {
    // SAFETY: caller contract.
    unsafe {
        let mut p = (*span).remote.swap(0, Ordering::Acquire) as *mut u8;
        if p.is_null() {
            return false;
        }
        while !p.is_null() {
            let Some(idx) = (*span).block_index(p) else {
                corrupt("remote free pointer")
            };
            if !(*span).is_allocated(idx) {
                corrupt("double free (remote)");
            }
            let next = decode(*(p as *const usize), p as usize);
            span_push(span, p, idx);
            p = next;
        }
        true
    }
}

/// # Safety
/// `span` must be a live span.
#[inline(always)]
unsafe fn span_has_free(span: *const Span) -> bool {
    // SAFETY: caller contract.
    unsafe { (*span).free != 0 || (*span).bump < (*span).capacity }
}

// ---------------------------------------------------------------------
// Orphans.

struct Orphans([*mut Span; NUM_CLASSES]);

/// Releases the empty orphans that no thread has adopted for a decay
/// period; their pages go straight back to the kernel.
fn decay_orphans(orphans: &mut Orphans, now: u64) {
    for class in 0..NUM_CLASSES {
        let mut span = orphans.0[class];
        while !span.is_null() {
            // SAFETY: spans on the orphan lists are live; the caller
            // holds the lock.
            unsafe {
                let next = (*span).next;
                if (*span).used == 0 && now.saturating_sub((*span).retained_at) > RETAIN_DECAY_MS {
                    list_remove(&mut orphans.0[class], span);
                    segment::release_idle_span(span, (*span).retained_at);
                }
                span = next;
            }
        }
    }
}

/// Whether the orphan list of `class` already holds an empty span.
fn orphans_has_empty(orphans: &Orphans, class: usize) -> bool {
    let mut span = orphans.0[class];
    while !span.is_null() {
        // SAFETY: spans on the orphan lists are live; the caller holds
        // the lock.
        unsafe {
            if (*span).used == 0 {
                return true;
            }
            span = (*span).next;
        }
    }
    false
}
// SAFETY: access is serialised by the mutex.
unsafe impl Send for Orphans {}
static ORPHANS: Mutex<Orphans> = Mutex::new(Orphans([ptr::null_mut(); NUM_CLASSES]));

/// Hands every span of `heap` to the orphan lists (or releases empty
/// ones). Called when a thread exits.
///
/// # Safety
/// `heap` must not be used again.
pub unsafe fn abandon(heap: *mut Heap) {
    // SAFETY: caller contract.
    unsafe {
        flush_remote(heap);
        for class in 0..NUM_CLASSES {
            let n = (*heap).cache[class].count as usize;
            if n != 0 {
                flush_cache(heap, class, n);
            }
        }
    }
    let mut orphans = ORPHANS.lock();
    let now = segment::coarse_ms();
    decay_orphans(&mut orphans, now);
    // The empty reserve goes to the orphan lists first (one empty span
    // per class), where the next thread adopts it with a single list pop
    // instead of a walk of the pool's segment bitmaps: a burst of
    // short-lived threads otherwise serialises on the pool lock.
    for tier in 0..TIERS {
        // SAFETY: the heap's lists are only touched by its thread.
        unsafe {
            let mut span = (*heap).empty[tier];
            while !span.is_null() {
                let next = (*span).next;
                let class = (*span).class as usize;
                if orphans_has_empty(&orphans, class) {
                    segment::release_span(span);
                } else {
                    segment::reinit_span(span, class);
                    (*span).owner.store(0, Ordering::Release);
                    (*span).is_full = false;
                    (*span).retained_at = now;
                    list_push(&mut orphans.0[class], span);
                }
                span = next;
            }
            (*heap).empty[tier] = ptr::null_mut();
            (*heap).empty_tail[tier] = ptr::null_mut();
        }
    }
    // SAFETY: as above.
    unsafe { (*heap).retained = 0 };
    for class in 0..NUM_CLASSES {
        // SAFETY: the heap's lists are only touched by its thread.
        let lists = unsafe {
            [
                ptr::addr_of_mut!((*heap).avail[class]),
                ptr::addr_of_mut!((*heap).full[class]),
            ]
        };
        for list in lists {
            // SAFETY: as above.
            unsafe {
                while !(*list).is_null() {
                    let span = *list;
                    list_remove(list, span);
                    span_collect_remote(span);
                    // Empty spans are kept for the next thread too (one
                    // per class): returning their pages costs a TLB
                    // shootdown, which short-lived threads would pay on
                    // every exit, and page faults on the next use.
                    if (*span).used == 0 && orphans_has_empty(&orphans, class) {
                        segment::release_span(span);
                    } else {
                        (*span).owner.store(0, Ordering::Release);
                        (*span).is_full = false;
                        (*span).retained_at = now;
                        list_push(&mut orphans.0[class], span);
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// Empty span reserve.

/// Puts an empty span into the heap's reserve, or gives it back when
/// the reserve is full.
///
/// # Safety
/// `span` must be empty and owned by `heap`, and on no list.
unsafe fn retain_span(heap: *mut Heap, span: *mut Span) {
    // SAFETY: caller contract.
    unsafe {
        let now = segment::coarse_ms();
        decay_retained(heap, now);
        let bytes = (*span).units as usize * segment::UNIT_SIZE;
        (*span).retained_at = now;
        // Make room by giving back the least recently freed spans (the
        // incoming one is the most likely to be needed again soon).
        // (`unlink_retained` lowers `retained`, through the pointer.)
        #[allow(clippy::while_immutable_condition)]
        while (*heap).retained + bytes > RETAIN_MAX {
            let mut victim: *mut Span = ptr::null_mut();
            for tier in 0..TIERS {
                let tail = (*heap).empty_tail[tier];
                if !tail.is_null() && (victim.is_null() || (*tail).units > (*victim).units) {
                    victim = tail;
                }
            }
            if victim.is_null() {
                segment::release_span(span);
                return;
            }
            unlink_retained(heap, victim);
            segment::release_span(victim);
        }
        let tier = tier_of((*span).class as usize);
        let head = (*heap).empty[tier];
        (*span).prev = ptr::null_mut();
        (*span).next = head;
        if head.is_null() {
            (*heap).empty_tail[tier] = span;
        } else {
            (*head).prev = span;
        }
        (*heap).empty[tier] = span;
        (*heap).retained += bytes;
    }
}

/// Gives back the retained spans that have been idle for too long (they
/// sit at the tails of the lists, oldest last).
///
/// # Safety
/// The heap must belong to the calling thread.
unsafe fn decay_retained(heap: *mut Heap, now: u64) {
    // SAFETY: caller contract.
    unsafe {
        for tier in 0..TIERS {
            loop {
                let tail = (*heap).empty_tail[tier];
                if tail.is_null() || now.saturating_sub((*tail).retained_at) <= RETAIN_DECAY_MS {
                    break;
                }
                unlink_retained(heap, tail);
                segment::release_idle_span(tail, (*tail).retained_at);
            }
        }
    }
}

/// Removes `span` from the heap's reserve.
///
/// # Safety
/// `span` must be in the reserve of `heap`.
unsafe fn unlink_retained(heap: *mut Heap, span: *mut Span) {
    // SAFETY: caller contract.
    unsafe {
        let tier = tier_of((*span).class as usize);
        let (prev, next) = ((*span).prev, (*span).next);
        if prev.is_null() {
            (*heap).empty[tier] = next;
        } else {
            (*prev).next = next;
        }
        if next.is_null() {
            (*heap).empty_tail[tier] = prev;
        } else {
            (*next).prev = prev;
        }
        (*span).prev = ptr::null_mut();
        (*span).next = ptr::null_mut();
        (*heap).retained -= (*span).units as usize * segment::UNIT_SIZE;
    }
}

/// Takes an empty span for `class` out of the heap's reserve, laid out
/// for that class.
///
/// # Safety
/// The heap must belong to the calling thread.
unsafe fn take_retained(heap: *mut Heap, class: usize) -> *mut Span {
    // SAFETY: caller contract.
    unsafe {
        let tier = tier_of(class);
        let span = (*heap).empty[tier];
        if span.is_null() {
            return span;
        }
        unlink_retained(heap, span);
        decay_retained(heap, segment::coarse_ms());
        segment::reinit_span(span, class);
        span
    }
}

// ---------------------------------------------------------------------
// Allocation.

/// Lets the heap's reserve decay every so often from the cache refill
/// and flush paths: the reserve normally decays when it is touched, but
/// a thread whose working set shrank and then settled would otherwise
/// hold its reserve forever. A coarse clock read every 16th refill or
/// flush costs about a nanosecond per allocation.
///
/// # Safety
/// The heap must belong to the calling thread.
#[inline]
unsafe fn maybe_decay(heap: *mut Heap) {
    // SAFETY: caller contract.
    unsafe {
        if (*heap).retained != 0 {
            (*heap).refills = (*heap).refills.wrapping_add(1);
            if (*heap).refills.is_multiple_of(16) {
                decay_retained(heap, segment::coarse_ms());
            }
        }
    }
}

/// The slow path of `malloc`: refills the class's cache from spans (a
/// batch, so the span is touched once for several allocations) and
/// returns one block.
#[cold]
#[inline(never)]
unsafe fn alloc_slow(heap: *mut Heap, class: usize) -> *mut u8 {
    // SAFETY: the heap belongs to the calling thread.
    unsafe {
        let cache = ptr::addr_of_mut!((*heap).cache[class]);
        if (*cache).cap == 0 {
            (*cache).cap = cache_cap(class);
        }
        let want = ((*cache).cap / 2).max(1) as usize;
        // The reserve normally decays when it is touched; a thread that
        // stops needing spans altogether (its working set shrank and
        // settled) would otherwise hold its reserve forever, so check it
        // every so often from here.
        maybe_decay(heap);
        let mut got = 0;
        while got < want {
            let span = next_span(heap, class);
            if span.is_null() {
                break;
            }
            while got < want {
                match span_pop_cached(span) {
                    Some(e) => {
                        (*cache).set(got, e);
                        got += 1;
                    }
                    None => break,
                }
            }
        }
        if got == 0 {
            return ptr::null_mut();
        }
        got -= 1;
        (*cache).count = got as u8;
        (*cache).get(got).take()
    }
}

/// Finds or creates a span of `class` with a free block, at the head of
/// the heap's avail list; null if memory is exhausted.
unsafe fn next_span(heap: *mut Heap, class: usize) -> *mut Span {
    // SAFETY: the heap belongs to the calling thread.
    unsafe {
        let avail = ptr::addr_of_mut!((*heap).avail[class]);
        let full = ptr::addr_of_mut!((*heap).full[class]);
        // Spans on the avail list: collect remote frees and use the first
        // one with room; move exhausted ones to the full list.
        while !(*avail).is_null() {
            let span = *avail;
            span_collect_remote(span);
            if span_has_free(span) {
                return span;
            }
            list_remove(avail, span);
            (*span).is_full = true;
            list_push(full, span);
        }
        // Full spans may have accumulated remote frees.
        let mut span = *full;
        while !span.is_null() {
            let next = (*span).next;
            if span_collect_remote(span) {
                list_remove(full, span);
                (*span).is_full = false;
                list_push(avail, span);
                return span;
            }
            span = next;
        }
        // Adopt an orphan (and let the ones nobody adopts decay).
        loop {
            let span = {
                let mut orphans = ORPHANS.lock();
                decay_orphans(&mut orphans, segment::coarse_ms());
                let span = orphans.0[class];
                if !span.is_null() {
                    list_remove(&mut orphans.0[class], span);
                    (*span).owner.store((*heap).id(), Ordering::Release);
                }
                span
            };
            if span.is_null() {
                break;
            }
            span_collect_remote(span);
            if span_has_free(span) {
                list_push(avail, span);
                return span;
            }
            (*span).is_full = true;
            list_push(full, span);
        }
        // A retained empty span, else a fresh one.
        let span = take_retained(heap, class);
        let span = if span.is_null() {
            match segment::alloc_span(class, (*heap).id()) {
                Some(span) => span,
                None => return ptr::null_mut(),
            }
        } else {
            span
        };
        list_push(avail, span);
        span
    }
}

/// Allocates `size` bytes with the default alignment. Returns null and
/// sets `errno` on failure. Inlined into its callers (`malloc` above
/// all) so the fast path is not a jump through a stub.
#[inline(always)]
pub fn alloc(size: usize) -> *mut u8 {
    if size > MAX_SMALL {
        return alloc_big_entry(size);
    }
    let class = class_for(size);
    let heap = current_heap();
    // SAFETY: the heap belongs to the calling thread.
    unsafe {
        let cache = ptr::addr_of_mut!((*heap).cache[class]);
        let n = (*cache).count;
        if n != 0 {
            let n = n - 1;
            (*cache).count = n;
            return (*cache).get(n as usize).take();
        }
        let p = alloc_slow(heap, class);
        if p.is_null() {
            Errno::ENOMEM.set();
        }
        p
    }
}

/// Allocates `size` bytes aligned to `align` (a power of two).
pub fn alloc_aligned(size: usize, align: usize) -> *mut u8 {
    if align <= 16 {
        return alloc(size);
    }
    if align <= crate::sys::MIN_PAGE_SIZE
        && let Some(class) = class_for_aligned(size, align)
    {
        return alloc(CLASS_SIZE[class] as usize);
    }
    // A large span starts on a unit boundary, which satisfies any
    // alignment up to the unit size.
    if align <= segment::UNIT_SIZE && size <= segment::LARGE_MAX {
        return finish(segment::alloc_large(size).map(|(p, _)| p));
    }
    finish(segment::alloc_huge(size, align).map(|(p, _)| p))
}

/// [`alloc`] for sizes above [`MAX_SMALL`], kept out of line so the
/// small-block fast path needs no stack frame.
#[cold]
#[inline(never)]
fn alloc_big_entry(size: usize) -> *mut u8 {
    finish(alloc_big(size).map(|(p, _)| p))
}

/// Allocates a block bigger than [`MAX_SMALL`]: a large span, or a huge
/// mapping beyond what a segment can hold. The flag says whether the
/// memory is known to be zero-filled.
fn alloc_big(size: usize) -> Option<(*mut u8, bool)> {
    // A big allocation is a natural point to let this thread's reserve
    // of small spans decay (the reserve otherwise only decays when the
    // small-block paths touch it).
    let heap = current_heap();
    // SAFETY: the heap belongs to the calling thread.
    unsafe {
        if (*heap).retained != 0 {
            decay_retained(heap, segment::coarse_ms());
        }
    }
    if size <= segment::LARGE_MAX {
        segment::alloc_large(size)
    } else {
        segment::alloc_huge(size, 16)
    }
}

/// Allocates `size` zeroed bytes.
pub fn alloc_zeroed(size: usize) -> *mut u8 {
    if size > MAX_SMALL {
        return match alloc_big(size) {
            Some((p, fresh)) => {
                // A fresh mapping is already zero; a recycled one is not.
                if !fresh {
                    // SAFETY: `p` has at least `size` bytes.
                    unsafe { ptr::write_bytes(p, 0, size) };
                }
                p
            }
            None => finish(None),
        };
    }
    let class = class_for(size);
    let heap = current_heap();
    // SAFETY: the heap belongs to the calling thread.
    unsafe {
        let span = (*heap).avail[class];
        if !span.is_null() {
            let (p, zero) = span_pop_zeroed(span);
            if !p.is_null() {
                if !zero {
                    ptr::write_bytes(p, 0, size);
                }
                return p;
            }
        }
        let p = alloc_slow(heap, class);
        if p.is_null() {
            Errno::ENOMEM.set();
            return p;
        }
        ptr::write_bytes(p, 0, size);
        p
    }
}

fn finish(p: Option<*mut u8>) -> *mut u8 {
    match p {
        Some(p) => p,
        None => {
            Errno::ENOMEM.set();
            ptr::null_mut()
        }
    }
}

/// Frees a block.
///
/// # Safety
/// `p` must have come from this allocator and not be freed already.
pub unsafe fn dealloc(p: *mut u8) {
    if p.is_null() {
        return;
    }
    // SAFETY: caller contract.
    unsafe {
        match segment::lookup(p) {
            Owner::Huge(h) => {
                if segment::huge_data(h) != p {
                    corrupt("free of interior pointer of a large block");
                }
                segment::free_huge(h);
            }
            Owner::Span(span) => {
                let Some(idx) = (*span).block_index(p) else {
                    corrupt("free of invalid pointer")
                };
                if (*span).class == segment::LARGE_CLASS {
                    segment::free_large(span, p);
                    return;
                }
                let heap = current_heap();
                if (*span).owner.load(Ordering::Acquire) == (*heap).id() {
                    if !(*span).is_allocated(idx) {
                        corrupt("double free");
                    }
                    (*span).mark_free(idx);
                    // Into the cache; flush half of it to the spans when
                    // it is full.
                    let class = (*span).class as usize;
                    let cache = ptr::addr_of_mut!((*heap).cache[class]);
                    if (*cache).cap == 0 {
                        (*cache).cap = cache_cap(class);
                    }
                    if (*cache).count >= (*cache).cap {
                        flush_cache(heap, class, ((*cache).cap / 2).max(1) as usize);
                    }
                    let n = (*cache).count as usize;
                    (*cache).set(n, Entry::new(p, (*span).bitmap, idx));
                    (*cache).count = (n + 1) as u8;
                } else {
                    // Not ours: batch it for the owner.
                    let n = (*heap).remote_count as usize;
                    if n == REMOTE_BUF {
                        flush_remote(heap);
                        (*heap).remote[0] =
                            core::mem::MaybeUninit::new(RemoteEntry { ptr: p, span });
                        (*heap).remote_count = 1;
                    } else {
                        (*heap).remote[n] =
                            core::mem::MaybeUninit::new(RemoteEntry { ptr: p, span });
                        (*heap).remote_count = (n + 1) as u8;
                    }
                }
            }
            Owner::Invalid => corrupt("free of pointer not from malloc"),
        }
    }
}

/// Returns `p` (block `idx` of `span`, owned by `heap`, its allocation
/// bit already clear) to the span's free list and keeps the heap's span
/// lists in order.
///
/// # Safety
/// As stated; the block must not be in the cache.
unsafe fn free_to_span(heap: *mut Heap, span: *mut Span, p: *mut u8, idx: u32) {
    // SAFETY: caller contract.
    unsafe {
        span_push_cached(span, p, idx);
        let class = (*span).class as usize;
        if (*span).is_full {
            list_remove(ptr::addr_of_mut!((*heap).full[class]), span);
            (*span).is_full = false;
            list_push(ptr::addr_of_mut!((*heap).avail[class]), span);
        } else if (*span).used == 0 {
            // Completely free: into the heap's reserve, where any class
            // of its tier can pick it up (the block cache keeps a block
            // freed and reallocated in a loop from ever getting here).
            list_remove(ptr::addr_of_mut!((*heap).avail[class]), span);
            retain_span(heap, span);
        }
    }
}

/// Pushes the buffered remote frees on their spans' remote stacks, one
/// chain (and one CAS) per span. Links are encoded like the local
/// list's, so a use-after-free write cannot redirect the owner's
/// collection at an arbitrary block.
///
/// # Safety
/// The heap must belong to the calling thread.
unsafe fn flush_remote(heap: *mut Heap) {
    // SAFETY: caller contract; buffered entries are live blocks of
    // other threads' spans.
    unsafe {
        let n = (*heap).remote_count as usize;
        let buf = (*heap).remote.as_mut_ptr() as *mut RemoteEntry;
        for i in 0..n {
            let first = *buf.add(i);
            if first.span.is_null() {
                continue;
            }
            // Chain every buffered block of this span: each links to the
            // next one found, the last to whatever the stack holds.
            let span = first.span;
            let head = first.ptr;
            let mut tail = first.ptr;
            for j in i + 1..n {
                let e = *buf.add(j);
                if e.span == span {
                    *(tail as *mut usize) = encode(e.ptr, tail as usize);
                    tail = e.ptr;
                    (*buf.add(j)).span = ptr::null_mut();
                }
            }
            let remote = &(*span).remote;
            let mut old = remote.load(Ordering::Relaxed);
            loop {
                *(tail as *mut usize) = encode(old as *mut u8, tail as usize);
                match remote.compare_exchange_weak(
                    old,
                    head as usize,
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => break,
                    Err(h) => old = h,
                }
            }
        }
        (*heap).remote_count = 0;
    }
}

/// Moves the oldest `n` entries of a class's cache to their spans.
///
/// # Safety
/// The heap must belong to the calling thread.
unsafe fn flush_cache(heap: *mut Heap, class: usize, n: usize) {
    // SAFETY: caller contract; cached blocks belong to spans this heap
    // owns.
    unsafe {
        let cache = ptr::addr_of_mut!((*heap).cache[class]);
        let count = (*cache).count as usize;
        let n = n.min(count);
        maybe_decay(heap);
        for i in 0..n {
            let e = (*cache).get(i);
            // The entry's bitmap byte says which span and block it is,
            // without another lookup of the pointer.
            let span = span_of_word(e.byte as *mut u64);
            let idx = e.index((*span).bitmap);
            free_to_span(heap, span, e.ptr(), idx);
        }
        (*cache).entries.copy_within(n..count, 0);
        (*cache).count = (count - n) as u8;
    }
}

/// Usable size of the block at `p`.
///
/// # Safety
/// `p` must be a live block from this allocator.
pub unsafe fn usable_size(p: *mut u8) -> usize {
    // SAFETY: caller contract.
    unsafe {
        match segment::lookup(p) {
            Owner::Huge(h) => segment::huge_usable_size(h),
            Owner::Span(span) => (*span).block_size as usize,
            Owner::Invalid => corrupt("malloc_usable_size of pointer not from malloc"),
        }
    }
}

/// Resizes a block, moving it if necessary.
///
/// # Safety
/// `p` must be null or a live block from this allocator.
pub unsafe fn realloc_impl(p: *mut u8, size: usize) -> *mut u8 {
    if p.is_null() {
        return alloc(size);
    }
    // SAFETY: caller contract.
    unsafe {
        let owner = segment::lookup(p);
        // A large span shrinks or grows in place when it can.
        if let Owner::Span(span) = owner
            && (*span).class == segment::LARGE_CLASS
            && segment::resize_large(span, size)
        {
            return p;
        }
        let old = usable_size(p);
        // Keep the block if it fits and would not waste most of it.
        if size <= old && (size >= old / 4 || old <= 128) {
            return p;
        }
        // Huge blocks are resized by the kernel instead of copied.
        if size > segment::LARGE_MAX
            && let Owner::Huge(h) = owner
            && let Some(q) = segment::realloc_huge(h, size)
        {
            return q;
        }
        let new = alloc(size);
        if new.is_null() {
            return new;
        }
        ptr::copy_nonoverlapping(p, new, old.min(size));
        dealloc(p);
        new
    }
}

// ---------------------------------------------------------------------
// C API.

/// `malloc(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn malloc(size: usize) -> *mut c_void {
    alloc(size) as *mut c_void
}

/// `free(3)`.
///
/// # Safety
/// `p` must be null or a live block from this allocator.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn free(p: *mut c_void) {
    // SAFETY: forwarded.
    unsafe { dealloc(p as *mut u8) }
}

/// `calloc(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn calloc(n: usize, size: usize) -> *mut c_void {
    let Some(total) = n.checked_mul(size) else {
        Errno::ENOMEM.set();
        return ptr::null_mut();
    };
    alloc_zeroed(total) as *mut c_void
}

/// `realloc(3)`.
///
/// # Safety
/// `p` must be null or a live block from this allocator.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn realloc(p: *mut c_void, size: usize) -> *mut c_void {
    // SAFETY: forwarded.
    unsafe { realloc_impl(p as *mut u8, size) as *mut c_void }
}

/// `reallocarray(3)`: `realloc` with overflow-checked multiplication.
///
/// # Safety
/// As for [`realloc`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn reallocarray(p: *mut c_void, n: usize, size: usize) -> *mut c_void {
    match n.checked_mul(size) {
        // SAFETY: forwarded.
        Some(total) => unsafe { realloc(p, total) },
        None => {
            Errno::ENOMEM.set();
            ptr::null_mut()
        }
    }
}

/// `posix_memalign(3)`.
///
/// # Safety
/// `out` must be a valid pointer.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn posix_memalign(out: *mut *mut c_void, align: usize, size: usize) -> c_int {
    if !align.is_power_of_two() || !align.is_multiple_of(core::mem::size_of::<*mut c_void>()) {
        return Errno::EINVAL.0;
    }
    let p = alloc_aligned(size, align);
    if p.is_null() {
        return Errno::ENOMEM.0;
    }
    // SAFETY: caller contract.
    unsafe { *out = p as *mut c_void };
    0
}

/// `aligned_alloc(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn aligned_alloc(align: usize, size: usize) -> *mut c_void {
    memalign(align, size)
}

/// `memalign(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn memalign(align: usize, size: usize) -> *mut c_void {
    if !align.is_power_of_two() {
        Errno::EINVAL.set();
        return ptr::null_mut();
    }
    alloc_aligned(size, align) as *mut c_void
}

/// `valloc(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn valloc(size: usize) -> *mut c_void {
    memalign(crate::sys::page_size(), size)
}

/// `malloc_usable_size(3)`.
///
/// # Safety
/// `p` must be null or a live block from this allocator.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn malloc_usable_size(p: *mut c_void) -> usize {
    if p.is_null() {
        return 0;
    }
    // SAFETY: forwarded.
    unsafe { usable_size(p as *mut u8) }
}

/// Locks all allocator-global state (for `fork`).
pub fn prefork() {
    // Same order as a thread exiting with a free span: `abandon` holds
    // ORPHANS while `release_span` takes the pool lock.
    ORPHANS.raw().lock();
    segment::pool_lock().lock();
    segment::huge_cache_lock().lock();
}

/// Unlocks the state taken by [`prefork`].
///
/// # Safety
/// Must follow a call to [`prefork`] on the same thread.
pub unsafe fn postfork() {
    // SAFETY: caller contract.
    unsafe {
        segment::huge_cache_lock().unlock();
        segment::pool_lock().unlock();
        ORPHANS.raw().unlock();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    fn fill(p: *mut u8, n: usize, b: u8) {
        // SAFETY: test blocks are large enough.
        unsafe { ptr::write_bytes(p, b, n) }
    }

    fn check(p: *mut u8, n: usize, b: u8) {
        // SAFETY: test blocks are large enough.
        let s = unsafe { core::slice::from_raw_parts(p, n) };
        assert!(s.iter().all(|&x| x == b), "block contents corrupted");
    }

    #[test]
    fn basic_alloc_free() {
        let p = alloc(10);
        assert!(!p.is_null());
        assert_eq!(p as usize % 16, 0);
        // SAFETY: live block.
        unsafe {
            assert_eq!(usable_size(p), 16);
            fill(p, 16, 0xab);
            dealloc(p);
        }
        let q = alloc(10);
        assert_eq!(p, q, "freed block should be reused first");
        // SAFETY: live block.
        unsafe { dealloc(q) };
        let z = alloc(0);
        assert!(!z.is_null());
        // SAFETY: live block.
        unsafe { dealloc(z) };
        // SAFETY: null is allowed.
        unsafe { dealloc(ptr::null_mut()) };
    }

    #[test]
    fn every_class_and_huge() {
        let mut blocks = Vec::new();
        for c in 0..NUM_CLASSES {
            let size = CLASS_SIZE[c] as usize;
            for s in [size - 15, size] {
                let p = alloc(s);
                assert!(!p.is_null());
                // SAFETY: live block.
                assert_eq!(unsafe { usable_size(p) }, size);
                fill(p, s, c as u8);
                blocks.push((p, s, c as u8));
            }
        }
        for s in [MAX_SMALL + 1, 1 << 20, 5 << 20] {
            let p = alloc(s);
            assert!(!p.is_null());
            // SAFETY: live block.
            assert!(unsafe { usable_size(p) } >= s);
            fill(p, s, 7);
            blocks.push((p, s, 7));
        }
        for &(p, s, b) in &blocks {
            check(p, s, b);
        }
        for (p, _, _) in blocks {
            // SAFETY: live block.
            unsafe { dealloc(p) };
        }
    }

    #[test]
    fn random_workload_against_shadow() {
        let mut rng = Rng(0xdead_beef);
        let mut live: Vec<(*mut u8, usize, u8)> = Vec::new();
        for step in 0..200_000 {
            let op = rng.below(100);
            if op < 55 || live.is_empty() {
                let size = match rng.below(10) {
                    0 => rng.below(200_000),
                    1..=3 => rng.below(5000),
                    _ => rng.below(200),
                };
                let p = if rng.below(4) == 0 {
                    let p = calloc(1, size) as *mut u8;
                    check(p, size, 0);
                    p
                } else {
                    alloc(size)
                };
                assert!(!p.is_null());
                assert_eq!(p as usize % 16, 0);
                let b = step as u8;
                fill(p, size, b);
                live.push((p, size, b));
            } else if op < 90 {
                let i = rng.below(live.len());
                let (p, size, b) = live.swap_remove(i);
                check(p, size, b);
                // SAFETY: live block.
                unsafe { dealloc(p) };
            } else {
                let i = rng.below(live.len());
                let (p, size, b) = live[i];
                check(p, size, b);
                let new_size = rng.below(size * 2 + 50);
                // SAFETY: live block.
                let q = unsafe { realloc_impl(p, new_size) };
                assert!(!q.is_null());
                check(q, size.min(new_size), b);
                fill(q, new_size, b);
                live[i] = (q, new_size, b);
            }
        }
        for (p, size, b) in live {
            check(p, size, b);
            // SAFETY: live block.
            unsafe { dealloc(p) };
        }
    }

    #[test]
    fn alignment() {
        for shift in 3..=22 {
            let align = 1usize << shift;
            for size in [1, 100, 5000, 200_000] {
                let mut out: *mut c_void = ptr::null_mut();
                // SAFETY: `out` is valid.
                assert_eq!(
                    unsafe { posix_memalign(&mut out, align, size) },
                    0,
                    "align {align} size {size}"
                );
                assert_eq!(out as usize % align, 0);
                fill(out as *mut u8, size, 3);
                // SAFETY: live block.
                unsafe { dealloc(out as *mut u8) };
            }
        }
        let mut out: *mut c_void = ptr::null_mut();
        // SAFETY: `out` is valid.
        unsafe {
            assert_eq!(posix_memalign(&mut out, 24, 10), Errno::EINVAL.0);
            assert_eq!(posix_memalign(&mut out, 4, 10), Errno::EINVAL.0);
            assert_eq!(posix_memalign(&mut out, 1 << 30, 10), Errno::ENOMEM.0);
        }
        let p = memalign(4096, 10);
        assert_eq!(p as usize % 4096, 0);
        // SAFETY: live block.
        unsafe { free(p) };
        assert!(memalign(3, 10).is_null());
    }

    #[test]
    fn overflow_checks() {
        assert!(calloc(usize::MAX / 2, 4).is_null());
        assert_eq!(Errno::get(), Errno::ENOMEM);
        // SAFETY: null pointer input.
        assert!(unsafe { reallocarray(ptr::null_mut(), usize::MAX, 2) }.is_null());
        assert!(alloc(usize::MAX - 100).is_null());
    }

    #[test]
    fn realloc_semantics() {
        // SAFETY: null is allowed for realloc.
        let p = unsafe { realloc_impl(ptr::null_mut(), 100) };
        fill(p, 100, 9);
        // SAFETY: live block.
        unsafe {
            let q = realloc_impl(p, 50);
            assert_eq!(p, q, "shrinking a little keeps the block");
            let r = realloc_impl(q, 100_000);
            assert_ne!(q, r);
            check(r, 50, 9);
            let s = realloc_impl(r, 10);
            assert_ne!(r, s, "shrinking a lot moves the block");
            check(s, 10, 9);
            dealloc(s);
        }
    }

    #[test]
    fn cross_thread_free_and_abandon() {
        // Blocks allocated here, freed on other threads, and vice versa.
        let mine: Vec<usize> = (0..1000).map(|i| alloc(i % 300) as usize).collect();
        let mine2 = mine.clone();
        let theirs = std::thread::spawn(move || {
            for &p in &mine2 {
                // SAFETY: live blocks, freed exactly once.
                unsafe { dealloc(p as *mut u8) };
            }
            let v: Vec<usize> = (0..2000).map(|i| alloc(i % 1000) as usize).collect();
            // Free half of them here so the thread exit path sees a
            // partially used heap.
            for &p in &v[..1000] {
                // SAFETY: live blocks.
                unsafe { dealloc(p as *mut u8) };
            }
            // Simulate thread exit for this thread's heap.
            // SAFETY: nothing on this thread allocates afterwards.
            unsafe { abandon(current_heap()) };
            v[1000..].to_vec()
        })
        .join()
        .unwrap();
        // Our blocks are on remote lists; allocating enough should collect
        // them. The other thread's blocks now belong to orphan spans.
        for &p in &theirs {
            // SAFETY: live blocks.
            unsafe { dealloc(p as *mut u8) };
        }
        let again: Vec<*mut u8> = (0..3000).map(|i| alloc(i % 1000)).collect();
        for p in again {
            // SAFETY: live blocks.
            unsafe { dealloc(p) };
        }
    }

    #[test]
    #[should_panic(expected = "double free")]
    fn double_free_is_detected() {
        let p = alloc(40);
        // SAFETY: the second free is the bug under test.
        unsafe {
            dealloc(p);
            dealloc(p);
        }
    }

    #[test]
    #[should_panic(expected = "invalid pointer")]
    fn interior_free_is_detected() {
        let p = alloc(40);
        // SAFETY: the interior free is the bug under test.
        unsafe { dealloc(p.add(8)) };
    }

    #[test]
    #[should_panic(expected = "heap corruption")]
    fn corrupted_free_list_is_detected() {
        let _keep = alloc(64); // keeps the span from being recycled
        let p = alloc(64);
        let q = alloc(64);
        // SAFETY: deliberately corrupting a free block.
        unsafe {
            dealloc(p);
            dealloc(q);
            // Move both from the cache to the span's free list, where the
            // links live inside the blocks; q is the list head.
            let heap = current_heap();
            let class = class_for(64);
            let n = (*heap).cache[class].count as usize;
            flush_cache(heap, class, n);
            *(q as *mut usize) = 0x4141_4141_4141_4141;
            let _ = alloc(64); // refills: pops q, then the smashed link
            let _ = alloc(64);
        }
    }
}
