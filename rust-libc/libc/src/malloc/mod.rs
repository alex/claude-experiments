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

/// A thread's allocator state.
#[repr(C)]
pub struct Heap {
    /// Spans that have (or may have, pending remote frees) free blocks.
    avail: [*mut Span; NUM_CLASSES],
    /// Spans with no locally free blocks.
    full: [*mut Span; NUM_CLASSES],
}

impl Heap {
    /// An empty heap.
    pub const fn new() -> Self {
        Heap {
            avail: [ptr::null_mut(); NUM_CLASSES],
            full: [ptr::null_mut(); NUM_CLASSES],
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
    let mut orphans = ORPHANS.lock();
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
                        list_push(&mut orphans.0[class], span);
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// Allocation.

/// The slow path of `malloc`: finds or creates a span with a free block.
#[cold]
#[inline(never)]
unsafe fn alloc_slow(heap: *mut Heap, class: usize) -> *mut u8 {
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
                return span_pop(span);
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
                return span_pop(span);
            }
            span = next;
        }
        // Adopt an orphan.
        loop {
            let span = {
                let mut orphans = ORPHANS.lock();
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
                return span_pop(span);
            }
            (*span).is_full = true;
            list_push(full, span);
        }
        // A fresh span.
        match segment::alloc_span(class, (*heap).id()) {
            Some(span) => {
                list_push(avail, span);
                span_pop(span)
            }
            None => ptr::null_mut(),
        }
    }
}

/// Allocates `size` bytes with the default alignment. Returns null and
/// sets `errno` on failure.
pub fn alloc(size: usize) -> *mut u8 {
    if size > MAX_SMALL {
        return finish(segment::alloc_huge(size, 16).map(|(p, _)| p));
    }
    let class = class_for(size);
    let heap = current_heap();
    // SAFETY: the heap belongs to the calling thread.
    unsafe {
        let span = (*heap).avail[class];
        if !span.is_null() {
            let p = span_pop(span);
            if !p.is_null() {
                return p;
            }
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
    if align <= crate::sys::PAGE_SIZE
        && let Some(class) = class_for_aligned(size, align)
    {
        return alloc(CLASS_SIZE[class] as usize);
    }
    finish(segment::alloc_huge(size, align).map(|(p, _)| p))
}

/// Allocates `size` zeroed bytes.
pub fn alloc_zeroed(size: usize) -> *mut u8 {
    if size > MAX_SMALL {
        return match segment::alloc_huge(size, 16) {
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
    let p = alloc(size);
    if !p.is_null() {
        // SAFETY: `p` has at least `size` bytes.
        unsafe { ptr::write_bytes(p, 0, size) };
    }
    p
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
                let heap = current_heap();
                if (*span).owner.load(Ordering::Acquire) == (*heap).id() {
                    if !(*span).is_allocated(idx) {
                        corrupt("double free");
                    }
                    span_push(span, p, idx);
                    let class = (*span).class as usize;
                    if (*span).is_full {
                        list_remove(ptr::addr_of_mut!((*heap).full[class]), span);
                        (*span).is_full = false;
                        list_push(ptr::addr_of_mut!((*heap).avail[class]), span);
                    } else if (*span).used == 0 {
                        // Completely free. The only span of its class is
                        // always kept (a block freed and reallocated in a
                        // loop must not fault every time). Otherwise a
                        // large span, whose blocks cost page faults
                        // anyway, is given back, and of the single-unit
                        // spans (256 KiB) exactly one empty one is kept,
                        // at the head of the list where the next
                        // allocations reuse it.
                        let avail = ptr::addr_of_mut!((*heap).avail[class]);
                        let head = *avail;
                        if (*span).units > 1 {
                            if head != span || !(*span).next.is_null() {
                                list_remove(avail, span);
                                segment::release_span(span);
                            }
                        } else if head != span {
                            list_remove(avail, span);
                            if (*head).used == 0 {
                                segment::release_span(span);
                            } else {
                                list_push(avail, span);
                            }
                        } else {
                            // A span that just came back from the full
                            // list is the head; the previous empty span
                            // is right behind it.
                            let next = (*span).next;
                            if !next.is_null() && (*next).used == 0 {
                                list_remove(avail, next);
                                segment::release_span(next);
                            }
                        }
                    }
                } else {
                    // Not ours: push on the owner's remote stack.
                    // Links are encoded like the local list's, so a
                    // use-after-free write cannot redirect the owner's
                    // collection at an arbitrary block.
                    let remote = &(*span).remote;
                    let mut head = remote.load(Ordering::Relaxed);
                    loop {
                        *(p as *mut usize) = encode(head as *mut u8, p as usize);
                        match remote.compare_exchange_weak(
                            head,
                            p as usize,
                            Ordering::Release,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => break,
                            Err(h) => head = h,
                        }
                    }
                }
            }
            Owner::Invalid => corrupt("free of pointer not from malloc"),
        }
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
        let old = usable_size(p);
        // Keep the block if it fits and would not waste most of it.
        if size <= old && (size >= old / 4 || old <= 128) {
            return p;
        }
        // Huge blocks are resized by the kernel instead of copied.
        if size > MAX_SMALL
            && let Owner::Huge(h) = segment::lookup(p)
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
    memalign(crate::sys::PAGE_SIZE, size)
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
        let p = alloc(64);
        let q = alloc(64);
        // SAFETY: deliberately corrupting a free block.
        unsafe {
            dealloc(p);
            dealloc(q);
            // q is now the list head; smash its link.
            *(q as *mut usize) = 0x4141_4141_4141_4141;
            let _ = alloc(64); // pops q
            let _ = alloc(64); // pops the smashed link
        }
    }
}
