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
//! * A span keeps no free list: every block has a two-bit state (free,
//!   cached, allocated) in the span's bitmap, so the allocator never
//!   reads or writes freed blocks. A thread refills its per-class cache
//!   by scanning the bitmap for free blocks and flushes it by clearing
//!   states, touching metadata only.
//! * Blocks freed by another thread are marked in the span's remote-free
//!   bitmap (one atomic `or` per batch and word) and collected by the
//!   owner when it looks for blocks.
//! * When a thread exits its spans are orphaned; any thread can adopt
//!   them later.
//!
//! # Hardening
//!
//! * No allocator metadata is stored in user memory, so overflowing or
//!   writing into a freed block cannot corrupt the allocator's state.
//! * Each block's state is tracked in its span's bitmap, so freeing a
//!   block twice (cached or not), freeing an interior pointer or a
//!   pointer that was never allocated is detected and aborts the process.
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
use core::sync::atomic::Ordering;
use segment::{Owner, STATE_ALLOCATED, STATE_CACHED, STATE_FREE, Span};

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
const RETAIN_MAX: usize = 16 << 20;

/// Retained spans idle for longer than this are given back whenever the
/// reserve is next touched.
const RETAIN_DECAY_MS: u64 = 250;

/// Most entries a per-class block cache holds.
const CACHE_MAX: usize = 128;

/// `calloc` of blocks up to this size takes a cached block and clears
/// it; bigger ones look for a block whose pages are known to be zero.
const CALLOC_CACHED_MAX: u32 = 512;

/// A cached block: the block itself and its state byte, so handing it
/// out is a store to the byte and nothing else.
#[derive(Clone, Copy)]
#[repr(C)]
struct Entry {
    ptr: *mut u8,
    /// The block's state byte in its span.
    byte: *mut u8,
}

impl Entry {
    #[inline(always)]
    fn new(ptr: *mut u8, states: *mut u8, idx: u32) -> Entry {
        Entry {
            ptr,
            // SAFETY: the span has a state byte for every block.
            byte: unsafe { states.add(idx as usize) },
        }
    }

    /// Marks the block allocated and returns it.
    ///
    /// # Safety
    /// The entry must be live (its span still owned by this thread).
    #[inline(always)]
    unsafe fn take(self) -> *mut u8 {
        // SAFETY: caller contract.
        unsafe { *self.byte = STATE_ALLOCATED };
        self.ptr
    }
}

/// Per-class caches of free blocks in front of the span machinery (the
/// idea of glibc's tcache and tcmalloc's per-thread caches), holding
/// blocks in the *cached* state. `malloc` pops one and marks it
/// allocated; `free` marks it cached after the usual validation and
/// pushes. Refills and flushes move several blocks at once, so the
/// span's states and the segment lookup are touched once per batch
/// rather than per call, and neither touches the blocks themselves. A
/// block freed twice is caught by its state whether it is cached or on
/// the span. The entry tables are the bulk of a [`Heap`] and are left
/// uninitialised (only `counts` says what is valid), so thread start-up
/// does not pay for them.
type CacheEntries = [core::mem::MaybeUninit<Entry>; CACHE_MAX];

/// Cache capacity per class: 128 blocks for the small classes, fewer as
/// the blocks grow so that at most 64 KiB or so is cached per class
/// (one block for the big classes: enough for a free/malloc pair to
/// hit, without pinning megabytes per thread).
const CACHE_CAP: [u8; NUM_CLASSES] = {
    let mut caps = [0u8; NUM_CLASSES];
    let mut c = 0;
    while c < NUM_CLASSES {
        let cap = (64 * 1024) / CLASS_SIZE[c] as usize;
        caps[c] = if cap < 1 {
            1
        } else if cap > CACHE_MAX {
            CACHE_MAX as u8
        } else {
            cap as u8
        };
        c += 1;
    }
    caps
};

/// The span whose state array `word` belongs to (it lies in the span's
/// first unit, and unit 0's header maps every unit to its span).
///
/// # Safety
/// `word` must point into the state array of a live span.
unsafe fn span_of_word(word: *mut u64) -> *mut Span {
    // SAFETY: caller contract.
    unsafe { segment::span_containing(word as *const u8) }
}

/// Frees of other threads' blocks waiting to be marked in their spans'
/// remote bitmaps in batches (one atomic `or` per bitmap word per batch
/// instead of one per block, the biggest cost of producer/consumer
/// hand-offs). A batch is flushed when it is full, when it holds more
/// than [`REMOTE_FLUSH_BYTES`] (a big block must get back to its owner
/// promptly: a thread that frees one large buffer per work item and
/// nothing else remote would otherwise strand dozens of them), and
/// whenever the thread's own caches are refilled or flushed.
const REMOTE_BUF: usize = 64;
/// Pending remote frees are flushed once they hold this many bytes.
const REMOTE_FLUSH_BYTES: usize = 32 << 10;

#[derive(Clone, Copy)]
#[repr(C)]
struct RemoteEntry {
    span: *mut Span,
    idx: u32,
}

/// A thread's allocator state.
#[repr(C)]
pub struct Heap {
    /// Valid entries in each class's cache.
    counts: [u8; NUM_CLASSES],
    remote_count: u8,
    /// Bytes of blocks in `remote`.
    remote_bytes: u32,
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
    /// When the heap last collected the remote frees of all its spans.
    collected_at: u64,
    /// Pending remote frees (see [`REMOTE_BUF`]).
    remote: [core::mem::MaybeUninit<RemoteEntry>; REMOTE_BUF],
    /// The block caches (see [`CacheEntries`]); last, and never
    /// initialised as a whole.
    cache: [CacheEntries; NUM_CLASSES],
}

impl Heap {
    /// Initialises the heap at `this` (the caches' entry tables are left
    /// as they are).
    ///
    /// # Safety
    /// `this` must be valid for writes and not in use.
    pub unsafe fn init(this: *mut Heap) {
        // SAFETY: caller contract; field by field so the entry tables
        // are not written.
        unsafe {
            ptr::addr_of_mut!((*this).counts).write([0; NUM_CLASSES]);
            ptr::addr_of_mut!((*this).remote_count).write(0);
            ptr::addr_of_mut!((*this).remote_bytes).write(0);
            ptr::addr_of_mut!((*this).avail).write([ptr::null_mut(); NUM_CLASSES]);
            ptr::addr_of_mut!((*this).full).write([ptr::null_mut(); NUM_CLASSES]);
            ptr::addr_of_mut!((*this).empty).write([ptr::null_mut(); TIERS]);
            ptr::addr_of_mut!((*this).empty_tail).write([ptr::null_mut(); TIERS]);
            ptr::addr_of_mut!((*this).retained).write(0);
            ptr::addr_of_mut!((*this).refills).write(0);
            ptr::addr_of_mut!((*this).collected_at).write(0);
        }
    }

    /// The entry table of `class`'s cache.
    #[inline(always)]
    fn entries(this: *mut Heap, class: usize) -> *mut core::mem::MaybeUninit<Entry> {
        // SAFETY: in bounds of the heap.
        unsafe {
            ptr::addr_of_mut!((*this).cache)
                .cast::<core::mem::MaybeUninit<Entry>>()
                .add(class * CACHE_MAX)
        }
    }

    #[inline(always)]
    fn id(&self) -> usize {
        self as *const Heap as usize
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

/// Bit 0 of every byte of a word of states.
const LOW_BITS: u64 = 0x0101_0101_0101_0101;

/// The free blocks of a word of eight states, as a mask of their bytes'
/// low bits (states only use the low two bits of a byte).
#[inline(always)]
fn free_blocks(word: u64) -> u64 {
    !(word | (word >> 1)) & LOW_BITS
}

/// Moves up to `want - got` free blocks of `span` into the cache table
/// `entries` (from slot `got` on) as cached blocks, lowest addresses
/// first, and returns the new count. Touches only the states.
///
/// # Safety
/// The calling thread must own `span`; `entries` must be its cache
/// table for the span's class.
unsafe fn span_take_cached(
    span: *mut Span,
    entries: *mut core::mem::MaybeUninit<Entry>,
    mut got: usize,
    want: usize,
) -> usize {
    // SAFETY: caller contract.
    unsafe {
        let s = &mut *span;
        let words = s.words as usize;
        let mut w = s.hint as usize;
        while got < want && w < words {
            let wp = (s.states as *mut u64).add(w);
            let mut word = *wp;
            let mut free = free_blocks(word);
            if free == 0 {
                w += 1;
                continue;
            }
            let mut taken = 0;
            while free != 0 && got < want {
                let low = free.trailing_zeros();
                free &= free - 1;
                word |= (STATE_CACHED as u64) << low;
                let idx = (w * 8) as u32 + low / 8;
                entries
                    .add(got)
                    .write(core::mem::MaybeUninit::new(Entry::new(
                        s.data.add(idx as usize * s.block_size as usize),
                        s.states,
                        idx,
                    )));
                got += 1;
                taken += 1;
                if idx >= s.bump {
                    s.bump = idx + 1;
                }
            }
            *wp = word;
            s.used += taken;
            if free == 0 {
                w += 1;
            }
        }
        s.hint = w as u32;
        got
    }
}

/// Takes one block of `span` straight into the allocated state, also
/// saying whether it is known to be zero-filled (never handed out since
/// the span's pages were fresh). Null if the span has none.
///
/// # Safety
/// The calling thread must own `span`.
#[inline]
unsafe fn span_pop_zeroed(span: *mut Span) -> (*mut u8, bool) {
    // SAFETY: caller contract.
    unsafe {
        let s = &mut *span;
        let words = s.words as usize;
        let mut w = s.hint as usize;
        while w < words {
            let wp = (s.states as *mut u64).add(w);
            let word = *wp;
            let free = free_blocks(word);
            if free == 0 {
                w += 1;
                continue;
            }
            let low = free.trailing_zeros();
            *wp = word | ((STATE_ALLOCATED as u64) << low);
            s.hint = w as u32;
            s.used += 1;
            let idx = (w * 8) as u32 + low / 8;
            let zero = s.fresh && idx >= s.bump;
            if idx >= s.bump {
                s.bump = idx + 1;
            }
            return (s.data.add(idx as usize * s.block_size as usize), zero);
        }
        s.hint = w as u32;
        (ptr::null_mut(), false)
    }
}

/// Marks block `idx` of `span` free (from cached or allocated).
///
/// # Safety
/// The calling thread must own `span`; `idx` must be a block that is
/// not free.
#[inline]
unsafe fn span_free_block(span: *mut Span, idx: u32) {
    // SAFETY: caller contract.
    unsafe {
        let s = &mut *span;
        s.set_state(idx, STATE_FREE);
        s.used -= 1;
        let w = idx / 8;
        if w < s.hint {
            s.hint = w;
        }
    }
}

/// Frees the blocks other threads have marked in the remote bitmap.
/// Returns true if any were collected.
///
/// # Safety
/// The calling thread must own `span`.
unsafe fn span_collect_remote(span: *mut Span) -> bool {
    // SAFETY: caller contract.
    unsafe {
        let s = &mut *span;
        let mut groups = s.remote_summary.swap(0, Ordering::Acquire);
        if groups == 0 {
            return false;
        }
        let wpg = s.wpg as usize;
        let remote_words = (s.capacity as usize).div_ceil(64);
        while groups != 0 {
            let g = groups.trailing_zeros() as usize;
            groups &= groups - 1;
            for w in g * wpg..((g + 1) * wpg).min(remote_words) {
                let mut bits = (*s.remote_bits.add(w)).swap(0, Ordering::Acquire);
                while bits != 0 {
                    let idx = (w * 64) as u32 + bits.trailing_zeros();
                    bits &= bits - 1;
                    if idx >= s.capacity || s.state(idx) != STATE_ALLOCATED {
                        corrupt("double free (remote)");
                    }
                    span_free_block(span, idx);
                }
            }
        }
        true
    }
}

/// # Safety
/// `span` must be a live span.
#[inline(always)]
unsafe fn span_has_free(span: *const Span) -> bool {
    // SAFETY: caller contract.
    unsafe { (*span).used < (*span).capacity }
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
            let n = (*heap).counts[class] as usize;
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

/// Housekeeping from the cache refill and flush paths: flushes pending
/// remote frees, and lets the heap's reserve decay every so often (the
/// reserve normally decays when it is touched, but a thread whose
/// working set shrank and then settled would otherwise hold its reserve
/// forever; a coarse clock read every 16th refill or flush costs about
/// a nanosecond per allocation).
///
/// # Safety
/// The heap must belong to the calling thread.
#[inline]
unsafe fn maybe_decay(heap: *mut Heap) {
    // SAFETY: caller contract.
    unsafe {
        // Pending remote frees go out now rather than when the batch
        // fills: this thread is active, and their owners may be waiting.
        if (*heap).remote_count != 0 {
            flush_remote(heap);
        }
        (*heap).refills = (*heap).refills.wrapping_add(1);
        if (*heap).refills.is_multiple_of(16) {
            let now = segment::coarse_ms();
            if (*heap).retained != 0 {
                decay_retained(heap, now);
            }
            if now.saturating_sub((*heap).collected_at) >= COLLECT_MS {
                (*heap).collected_at = now;
                collect_all_remote(heap);
            }
        }
    }
}

/// How often a heap sweeps all its spans for blocks other threads have
/// freed (see [`collect_all_remote`]).
const COLLECT_MS: u64 = 250;

/// Collects the remote frees of every span of the heap, giving spans that
/// became empty to the reserve (from where they decay). Remote frees are
/// normally collected when the owner looks for blocks of that class; a
/// thread that keeps allocating other classes would otherwise never
/// reclaim memory that other threads freed for it, so this runs every
/// [`COLLECT_MS`] from the refill and flush paths. Its cost is one atomic
/// read per span, so a heap with thousands of spans pays tens of
/// microseconds per period.
///
/// # Safety
/// The heap must belong to the calling thread.
unsafe fn collect_all_remote(heap: *mut Heap) {
    // SAFETY: caller contract.
    unsafe {
        for class in 0..NUM_CLASSES {
            let avail = ptr::addr_of_mut!((*heap).avail[class]);
            let full = ptr::addr_of_mut!((*heap).full[class]);
            let mut span = *full;
            while !span.is_null() {
                let next = (*span).next;
                if span_collect_remote(span) {
                    list_remove(full, span);
                    (*span).is_full = false;
                    if (*span).used == 0 {
                        retain_span(heap, span);
                    } else {
                        list_push(avail, span);
                    }
                }
                span = next;
            }
            let mut span = *avail;
            while !span.is_null() {
                let next = (*span).next;
                if span_collect_remote(span) && (*span).used == 0 {
                    list_remove(avail, span);
                    retain_span(heap, span);
                }
                span = next;
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
        let entries = Heap::entries(heap, class);
        let want = (CACHE_CAP[class] / 2).max(1) as usize;
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
            got = span_take_cached(span, entries, got, want);
        }
        if got == 0 {
            Errno::ENOMEM.set();
            return ptr::null_mut();
        }
        got -= 1;
        (*heap).counts[class] = got as u8;
        (*entries.add(got)).assume_init().take()
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
        debug_assert!(class < NUM_CLASSES);
        let count = ptr::addr_of_mut!((*heap).counts).cast::<u8>().add(class);
        let n = *count;
        if n != 0 {
            let n = n - 1;
            *count = n;
            return (*Heap::entries(heap, class).add(n as usize))
                .assume_init()
                .take();
        }
        alloc_slow(heap, class)
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
        let now = segment::coarse_ms();
        if (*heap).retained != 0 {
            decay_retained(heap, now);
        }
        if now.saturating_sub((*heap).collected_at) >= COLLECT_MS {
            (*heap).collected_at = now;
            collect_all_remote(heap);
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
    // Clearing a small block costs less than bypassing the cache to
    // find one that is known to be zero.
    if CLASS_SIZE[class] <= CALLOC_CACHED_MAX {
        let p = alloc(size);
        if !p.is_null() {
            // Clear the whole (16-byte aligned) block with a handful of
            // wide stores rather than a call to `memset`.
            // SAFETY: the block holds `CLASS_SIZE[class]` bytes.
            unsafe {
                let words = CLASS_SIZE[class] as usize / 16;
                for i in 0..words {
                    (p as *mut u128).add(i).write(0);
                }
            }
        }
        return p;
    }
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
/// Only the common case (a block of a span this thread owns, with room
/// in the cache) is handled here; everything else is a tail call into a
/// cold function, so this path needs no stack frame or saved registers.
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
            Owner::Huge(h) => dealloc_huge(h, p),
            Owner::Span(span) => {
                let Some(idx) = (*span).block_index(p) else {
                    corrupt("free of invalid pointer")
                };
                let class = (*span).class as usize;
                if class == segment::LARGE_CLASS as usize {
                    return segment::free_large(span, p);
                }
                let heap = current_heap();
                if (*span).owner.load(Ordering::Acquire) != (*heap).id() {
                    return dealloc_remote(heap, span, idx);
                }
                let byte = (*span).state_byte(idx);
                if byte.load(Ordering::Relaxed) != STATE_ALLOCATED {
                    corrupt("double free");
                }
                byte.store(STATE_CACHED, Ordering::Relaxed);
                // Into the cache; flush half of it to the spans when it
                // is full.
                debug_assert!(class < NUM_CLASSES);
                let count = ptr::addr_of_mut!((*heap).counts).cast::<u8>().add(class);
                let n = *count as usize;
                if n >= *CACHE_CAP.get_unchecked(class) as usize {
                    return dealloc_full(heap, class, p, byte.as_ptr());
                }
                Heap::entries(heap, class)
                    .add(n)
                    .write(core::mem::MaybeUninit::new(Entry {
                        ptr: p,
                        byte: byte.as_ptr(),
                    }));
                *count = (n + 1) as u8;
            }
            Owner::Invalid => corrupt("free of pointer not from malloc"),
        }
    }
}

/// `free` of a huge block.
///
/// # Safety
/// `h` must be a live huge header.
#[cold]
#[inline(never)]
unsafe fn dealloc_huge(h: *mut segment::Header, p: *mut u8) {
    // SAFETY: caller contract.
    unsafe {
        if segment::huge_data(h) != p {
            corrupt("free of interior pointer of a large block");
        }
        segment::free_huge(h);
    }
}

/// `free` into a full cache: flushes half of it first.
///
/// # Safety
/// As for `dealloc`; the block's state is already cached.
#[inline(never)]
unsafe fn dealloc_full(heap: *mut Heap, class: usize, p: *mut u8, byte: *mut u8) {
    // SAFETY: caller contract.
    unsafe {
        flush_cache(heap, class, (CACHE_CAP[class] as usize / 2).max(1));
        let n = (*heap).counts[class] as usize;
        Heap::entries(heap, class)
            .add(n)
            .write(core::mem::MaybeUninit::new(Entry { ptr: p, byte }));
        (*heap).counts[class] = (n + 1) as u8;
    }
}

/// `free` of a block owned by another thread: batched for the owner.
/// The state is the owner's to change, but a block that is not allocated
/// is already a double free. Out of line (but not cold: for a consumer
/// thread this is the whole of `free`).
///
/// # Safety
/// `span` must be a live span and `idx` one of its blocks.
#[inline(never)]
unsafe fn dealloc_remote(heap: *mut Heap, span: *mut Span, idx: u32) {
    // SAFETY: caller contract.
    unsafe {
        if (*span).state(idx) != STATE_ALLOCATED {
            corrupt("double free (remote)");
        }
        let n = (*heap).remote_count as usize;
        (*heap).remote[n] = core::mem::MaybeUninit::new(RemoteEntry { span, idx });
        (*heap).remote_count = (n + 1) as u8;
        (*heap).remote_bytes += (*span).block_size;
        if n + 1 == REMOTE_BUF || (*heap).remote_bytes as usize >= REMOTE_FLUSH_BYTES {
            flush_remote(heap);
        }
    }
}

/// Marks block `idx` of `span` (owned by `heap`, cached) free and keeps
/// the heap's span lists in order.
///
/// # Safety
/// As stated; the block must no longer be in the cache.
unsafe fn free_to_span(heap: *mut Heap, span: *mut Span, idx: u32) {
    // SAFETY: caller contract.
    unsafe {
        span_free_block(span, idx);
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
    /// A (span, remote bitmap word) group of the batch.
    #[derive(Clone, Copy)]
    struct Group {
        span: *mut Span,
        word: u32,
        bits: u64,
    }
    // SAFETY: caller contract; buffered entries name live blocks of
    // other threads' spans.
    unsafe {
        let n = (*heap).remote_count as usize;
        let buf = (*heap).remote.as_ptr() as *const RemoteEntry;
        // Group the batch by bitmap word in a small open-addressing table
        // (one pass), then one atomic `or` per word and one per span's
        // summary.
        let mut groups = [Group {
            span: ptr::null_mut(),
            word: 0,
            bits: 0,
        }; REMOTE_BUF];
        for i in 0..n {
            let e = *buf.add(i);
            let word = e.idx / 64;
            let mut slot = ((e.span as usize >> 6) ^ word as usize) % REMOTE_BUF;
            loop {
                let g = &mut groups[slot];
                if g.span.is_null() {
                    *g = Group {
                        span: e.span,
                        word,
                        bits: 0,
                    };
                }
                if g.span == e.span && g.word == word {
                    g.bits |= 1 << (e.idx % 64);
                    break;
                }
                slot = (slot + 1) % REMOTE_BUF;
            }
        }
        for g in groups.iter().filter(|g| !g.span.is_null()) {
            let span = g.span;
            let word = &*(*span).remote_bits.add(g.word as usize);
            if word.fetch_or(g.bits, Ordering::AcqRel) & g.bits != 0 {
                corrupt("double free (remote)");
            }
        }
        // One summary update per span: the summary word is the one line
        // every freeing thread and the owner share.
        for i in 0..REMOTE_BUF {
            let g = groups[i];
            if g.span.is_null() {
                continue;
            }
            let wpg = (*g.span).wpg as u32;
            let mut summary = 1u64 << (g.word / wpg);
            for h in groups[i + 1..].iter_mut() {
                if h.span == g.span {
                    summary |= 1 << (h.word / wpg);
                    h.span = ptr::null_mut();
                }
            }
            (*g.span)
                .remote_summary
                .fetch_or(summary, Ordering::Release);
        }
        (*heap).remote_count = 0;
        (*heap).remote_bytes = 0;
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
        let entries = Heap::entries(heap, class);
        let count = (*heap).counts[class] as usize;
        let n = n.min(count);
        maybe_decay(heap);
        // The entry's state byte says which span and block it is,
        // without another lookup of the pointer; consecutive entries
        // usually belong to the same span, so the lookup is skipped while
        // the byte stays within the last span's state array.
        let mut span: *mut Span = ptr::null_mut();
        let (mut lo, mut hi) = (0usize, 0usize);
        for i in 0..n {
            let e = (*entries.add(i)).assume_init();
            let b = e.byte as usize;
            if b < lo || b >= hi {
                span = span_of_word(e.byte as *mut u64);
                lo = (*span).states as usize;
                hi = lo + (*span).capacity as usize;
            }
            free_to_span(heap, span, (b - lo) as u32);
        }
        ptr::copy(entries.add(n), entries, count - n);
        (*heap).counts[class] = (count - n) as u8;
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
    #[should_panic(expected = "double free")]
    fn double_free_of_cached_block_is_detected() {
        let p = alloc(64);
        let q = alloc(64);
        // SAFETY: the second free of `p` is the bug under test.
        unsafe {
            dealloc(p);
            dealloc(q);
            // Both sit in the cache now (states: cached).
            dealloc(p);
        }
    }

    #[test]
    fn freed_block_contents_are_not_trusted() {
        // Nothing the program writes into a freed block can affect the
        // allocator: there is no metadata in user memory to corrupt.
        let _keep = alloc(64);
        let blocks: Vec<*mut u8> = (0..200).map(|_| alloc(64)).collect();
        for &p in &blocks {
            // SAFETY: live block, then deliberately scribbled after free.
            unsafe {
                dealloc(p);
                ptr::write_bytes(p, 0x41, 64);
            }
        }
        let again: Vec<*mut u8> = (0..200).map(|_| alloc(64)).collect();
        for &p in &again {
            assert_eq!(p as usize % 16, 0);
            // SAFETY: live block.
            unsafe { dealloc(p) };
        }
        // SAFETY: live block.
        unsafe { dealloc(_keep) };
    }
}
