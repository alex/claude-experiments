//! Segments, spans and huge mappings.
//!
//! All memory handed out by the allocator lives in *segments*: 16 MiB
//! regions aligned to their size, so that the segment of any pointer is
//! found by masking. A segment is either:
//!
//! * a **normal segment**, split into 64 units of 256 KiB. Spans of one or
//!   four consecutive units each serve a single size class. The segment
//!   header at the start of the segment holds the per-span metadata, so
//!   no metadata is ever adjacent to user data;
//! * a **huge mapping** for a single allocation larger than
//!   [`MAX_SMALL`](super::classes::MAX_SMALL), with only the small
//!   [`Header`] in its first page.
//!
//! Each span starts with an allocation bitmap (one bit per block) followed
//! by the page-aligned block area. The bitmap makes double and invalid
//! frees detectable.

use super::classes::{CLASS_INV, CLASS_SIZE, units_for_class};
use crate::sync::{Mutex, RawMutex};
use crate::sys::{
    self, MAP_ANONYMOUS, MAP_NORESERVE, MAP_PRIVATE, PAGE_SIZE, PROT_READ, PROT_WRITE,
};
use core::ptr;
use core::sync::atomic::{AtomicU8, AtomicUsize, Ordering};

/// Size of one unit.
pub const UNIT_SIZE: usize = 256 * 1024;
/// Size (and alignment) of a segment.
pub const SEGMENT_SIZE: usize = 16 * 1024 * 1024;
/// Units per normal segment.
pub const UNITS: usize = SEGMENT_SIZE / UNIT_SIZE;
/// Bytes at the start of a normal segment reserved for the header.
const HEADER_SIZE: usize = 8192;
/// Bytes at the start of a huge mapping reserved for the header.
const HUGE_HEADER_SIZE: usize = PAGE_SIZE;

const MAGIC_NORMAL: usize = 0x5a5a_a11c_5e6d_0001;
const MAGIC_HUGE: usize = 0x5a5a_a11c_5e6d_0002;

/// The part of a segment header shared by normal segments and huge
/// mappings.
#[repr(C)]
pub struct Header {
    magic: usize,
    /// Huge mappings: total mapped length. Normal segments: unused.
    map_len: usize,
    /// Huge mappings: start of user data. Normal segments: unused.
    data: *mut u8,
}

/// A normal segment's header.
#[repr(C)]
pub struct Segment {
    header: Header,
    /// Next segment in the global pool.
    next: *mut Segment,
    /// Bit `i` set = unit `i` is free. Protected by the pool lock.
    free_units: u64,
    /// For each unit, the index of the first unit of its span. Only
    /// meaningful for allocated units.
    span_of: [AtomicU8; UNITS],
    spans: [Span; UNITS],
}

const _: () = assert!(core::mem::size_of::<Segment>() <= HEADER_SIZE);
const _: () = assert!(core::mem::size_of::<Header>() <= HUGE_HEADER_SIZE);

/// Metadata of a span. Lives in the segment header, indexed by the
/// span's first unit.
#[repr(C)]
pub struct Span {
    /// Block size in bytes; 0 for a span that is not allocated.
    pub block_size: u32,
    /// Size class.
    pub class: u8,
    /// Units in this span.
    pub units: u8,
    /// True while the span is on its heap's `full` list.
    pub is_full: bool,
    /// Number of blocks in the block area.
    pub capacity: u32,
    /// Blocks `[bump, capacity)` have never been handed out.
    pub bump: u32,
    /// Blocks currently allocated, as seen by the owning heap (remote
    /// frees are not subtracted until collected).
    pub used: u32,
    /// Head of the local free list, encoded (see `Heap`).
    pub free: usize,
    /// Head of the lock-free list of blocks freed by other threads.
    pub remote: AtomicUsize,
    /// The owning heap, or null when orphaned.
    pub owner: AtomicUsize,
    /// Previous span in the owning heap's per-class list (or orphan list).
    pub prev: *mut Span,
    /// Next span in the owning heap's per-class list (or orphan list).
    pub next: *mut Span,
    /// Allocation bitmap, one bit per block.
    pub bitmap: *mut u64,
    /// Start of the page-aligned block area.
    pub data: *mut u8,
}

impl Span {
    #[allow(clippy::declare_interior_mutable_const)]
    const EMPTY: Span = Span {
        block_size: 0,
        class: 0,
        units: 0,
        is_full: false,
        capacity: 0,
        bump: 0,
        used: 0,
        free: 0,
        remote: AtomicUsize::new(0),
        owner: AtomicUsize::new(0),
        prev: ptr::null_mut(),
        next: ptr::null_mut(),
        bitmap: ptr::null_mut(),
        data: ptr::null_mut(),
    };

    /// End of the block area.
    #[inline]
    pub fn data_end(&self) -> *mut u8 {
        // SAFETY: stays within the span.
        unsafe {
            self.data
                .add(self.capacity as usize * self.block_size as usize)
        }
    }

    /// Index of the block containing `p`, if `p` is a valid block start.
    #[inline]
    pub fn block_index(&self, p: *mut u8) -> Option<u32> {
        let off = (p as usize).wrapping_sub(self.data as usize);
        let bs = self.block_size as usize;
        if bs == 0 {
            return None;
        }
        // Division by multiplication (see `CLASS_INV`); the multiply-back
        // check makes the result exact for any `off`, valid or not.
        let idx = ((off as u64).wrapping_mul(CLASS_INV[self.class as usize]) >> 40) as usize;
        if idx >= self.bump as usize || idx * bs != off {
            None
        } else {
            Some(idx as u32)
        }
    }

    /// Tests the allocation bit of block `idx`.
    #[inline]
    pub fn is_allocated(&self, idx: u32) -> bool {
        // SAFETY: the bitmap has `capacity` bits.
        unsafe { *self.bitmap.add(idx as usize / 64) & (1 << (idx % 64)) != 0 }
    }

    /// Sets the allocation bit of block `idx`.
    #[inline]
    pub fn mark_allocated(&mut self, idx: u32) {
        // SAFETY: the bitmap has `capacity` bits.
        unsafe { *self.bitmap.add(idx as usize / 64) |= 1 << (idx % 64) }
    }

    /// Clears the allocation bit of block `idx`.
    #[inline]
    pub fn mark_free(&mut self, idx: u32) {
        // SAFETY: the bitmap has `capacity` bits.
        unsafe { *self.bitmap.add(idx as usize / 64) &= !(1 << (idx % 64)) }
    }
}

/// Global pool of normal segments.
struct Pool {
    head: *mut Segment,
}

// SAFETY: access is serialised by the mutex.
unsafe impl Send for Pool {}

static POOL: Mutex<Pool> = Mutex::new(Pool {
    head: ptr::null_mut(),
});

/// Recently freed huge mappings, kept for reuse so that programs which
/// repeatedly allocate and free large blocks do not pay for `mmap`,
/// `munmap` and the page faults of a fresh mapping every time. Entries
/// keep their contents (like any other freed memory); `calloc` zeroes
/// them explicitly.
struct HugeCache {
    /// `(base, mapping length)`.
    entries: [(usize, usize); HUGE_CACHE_SLOTS],
    count: usize,
}

const HUGE_CACHE_SLOTS: usize = 8;
/// Mappings larger than this always go back to the kernel.
const HUGE_CACHE_MAX_LEN: usize = 64 << 20;

static HUGE_CACHE: Mutex<HugeCache> = Mutex::new(HugeCache {
    entries: [(0, 0); HUGE_CACHE_SLOTS],
    count: 0,
});

/// Takes the smallest cached mapping of at least `len` bytes that does
/// not waste more than half of itself.
fn take_cached(len: usize) -> Option<(*mut u8, usize)> {
    let mut cache = HUGE_CACHE.lock();
    let mut best: Option<usize> = None;
    for i in 0..cache.count {
        let l = cache.entries[i].1;
        if l >= len && l <= 2 * len && best.is_none_or(|b| l < cache.entries[b].1) {
            best = Some(i);
        }
    }
    let i = best?;
    let entry = cache.entries[i];
    cache.count -= 1;
    cache.entries[i] = cache.entries[cache.count];
    Some((entry.0 as *mut u8, entry.1))
}

/// Maps `len` bytes aligned to [`SEGMENT_SIZE`] by over-allocating and
/// trimming. Returns the mapping's start.
fn map_aligned(len: usize) -> Option<*mut u8> {
    let total = len.checked_add(SEGMENT_SIZE)?;
    // SAFETY: fresh anonymous mapping.
    let base = unsafe {
        sys::mmap(
            ptr::null_mut(),
            total,
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
            -1,
            0,
        )
    }
    .ok()?;
    let start = (base as usize + SEGMENT_SIZE - 1) & !(SEGMENT_SIZE - 1);
    let head = start - base as usize;
    let tail = total - head - len;
    // SAFETY: trimming parts of our own fresh mapping.
    unsafe {
        if head > 0 {
            let _ = sys::munmap(base, head);
        }
        if tail > 0 {
            let _ = sys::munmap((start + len) as *mut u8, tail);
        }
    }
    Some(start as *mut u8)
}

/// Creates a new normal segment with every unit free.
fn new_segment() -> Option<*mut Segment> {
    let seg = map_aligned(SEGMENT_SIZE)? as *mut Segment;
    // SAFETY: the mapping is fresh, zeroed and large enough for the header.
    unsafe {
        ptr::addr_of_mut!((*seg).header).write(Header {
            magic: MAGIC_NORMAL,
            map_len: SEGMENT_SIZE,
            data: ptr::null_mut(),
        });
        ptr::addr_of_mut!((*seg).next).write(ptr::null_mut());
        ptr::addr_of_mut!((*seg).free_units).write(u64::MAX);
        for i in 0..UNITS {
            ptr::addr_of_mut!((*seg).span_of[i]).write(AtomicU8::new(0));
            ptr::addr_of_mut!((*seg).spans[i]).write(Span::EMPTY);
        }
    }
    Some(seg)
}

/// Finds `n` consecutive free units in `free`, returning the first index.
fn find_run(free: u64, n: usize) -> Option<usize> {
    let mask = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
    (0..=UNITS - n).find(|&i| free & (mask << i) == mask << i)
}

/// Allocates and initialises a span for `class`, owned by `owner`.
pub fn alloc_span(class: usize, owner: usize) -> Option<*mut Span> {
    let units = units_for_class(class);
    let mut pool = POOL.lock();
    let mut seg = pool.head;
    let (seg, first) = loop {
        if seg.is_null() {
            let s = new_segment()?;
            // SAFETY: `s` is a fresh segment; linking it into the pool.
            unsafe {
                (*s).next = pool.head;
            }
            pool.head = s;
            seg = s;
        }
        // SAFETY: segments in the pool are valid while the lock is held.
        let free = unsafe { (*seg).free_units };
        if let Some(first) = find_run(free, units) {
            break (seg, first);
        }
        // SAFETY: as above.
        seg = unsafe { (*seg).next };
    };
    let mask = ((1u64 << units) - 1) << first;
    // SAFETY: the units were free and are now ours; all writes are to the
    // header (under the pool lock) or to the span's own memory.
    unsafe {
        (*seg).free_units &= !mask;
        for u in first..first + units {
            (*seg).span_of[u].store(first as u8, Ordering::Relaxed);
        }
        let span = ptr::addr_of_mut!((*seg).spans[first]);
        let block_size = CLASS_SIZE[class] as usize;
        let mut start = seg as usize + first * UNIT_SIZE;
        let end = start + units * UNIT_SIZE;
        if first == 0 {
            start += HEADER_SIZE;
        }
        // Capacity, taking the bitmap page(s) into account: with one bit
        // per block a page of bitmap covers 32768 blocks, and even the
        // smallest class fits fewer than that per unit.
        let max_blocks = (end - start) / block_size;
        let bitmap_bytes = max_blocks.div_ceil(64) * 8;
        let data = (start + bitmap_bytes).next_multiple_of(PAGE_SIZE);
        let capacity = ((end - data) / block_size) as u32;
        ptr::write_bytes(start as *mut u8, 0, bitmap_bytes);
        span.write(Span {
            block_size: block_size as u32,
            class: class as u8,
            units: units as u8,
            is_full: false,
            capacity,
            bump: 0,
            used: 0,
            free: 0,
            remote: AtomicUsize::new(0),
            owner: AtomicUsize::new(owner),
            prev: ptr::null_mut(),
            next: ptr::null_mut(),
            bitmap: start as *mut u64,
            data: data as *mut u8,
        });
        Some(span)
    }
}

/// Returns a completely free span's units to its segment, and the
/// segment to the kernel if it became empty (and is not the only one).
///
/// # Safety
/// `span` must be an allocated span no heap references any more.
pub unsafe fn release_span(span: *mut Span) {
    let seg = segment_of(span as *const u8) as *mut Segment;
    // SAFETY: `span` lives in `seg`'s header.
    let first = unsafe {
        (span as usize - ptr::addr_of!((*seg).spans) as usize) / core::mem::size_of::<Span>()
    };
    let mut pool = POOL.lock();
    // SAFETY: the pool lock protects the segment's unit bookkeeping.
    unsafe {
        let units = (*span).units as usize;
        // Poison the metadata so a stale free into this span is caught.
        (*span).block_size = 0;
        (*span).capacity = 0;
        (*span).bump = 0;
        (*span).owner.store(0, Ordering::Relaxed);
        let mask = ((1u64 << units) - 1) << first;
        (*seg).free_units |= mask;
        // Let the kernel reclaim the pages of large spans. The segment
        // header at the start of unit 0 must of course be kept.
        if units > 1 {
            let mut start = seg as usize + first * UNIT_SIZE;
            let end = start + units * UNIT_SIZE;
            if first == 0 {
                start += HEADER_SIZE;
            }
            madvise_dontneed(start as *mut u8, end - start);
        }
        if (*seg).free_units == u64::MAX && (pool.head != seg || !(*seg).next.is_null()) {
            // Unlink and unmap.
            let mut link = &mut pool.head as *mut *mut Segment;
            while *link != seg {
                link = ptr::addr_of_mut!((**link).next);
            }
            *link = (*seg).next;
            let _ = sys::munmap(seg as *mut u8, SEGMENT_SIZE);
        }
    }
}

fn madvise_dontneed(addr: *mut u8, len: usize) {
    const MADV_DONTNEED: usize = 4;
    // SAFETY: the range is our own mapping and currently unused.
    unsafe {
        crate::arch::syscall3(crate::arch::nr::MADVISE, addr as usize, len, MADV_DONTNEED);
    }
}

/// The segment (or huge mapping) header containing `p`.
#[inline]
pub fn segment_of(p: *const u8) -> *const Header {
    (p as usize & !(SEGMENT_SIZE - 1)) as *const Header
}

/// What a pointer belongs to.
pub enum Owner {
    /// A block in a span of a normal segment.
    Span(*mut Span),
    /// A huge mapping.
    Huge(*mut Header),
    /// Not one of ours.
    Invalid,
}

/// Classifies `p`. Reading the header is only sound if `p` really came
/// from this allocator (the header page of a foreign pointer's "segment"
/// may not be mapped), which is the same contract C's `free` has.
///
/// # Safety
/// `p` must have been returned by this allocator and not yet freed.
pub unsafe fn lookup(p: *mut u8) -> Owner {
    let header = segment_of(p);
    // SAFETY: caller contract.
    unsafe {
        match (*header).magic {
            MAGIC_HUGE => Owner::Huge(header as *mut Header),
            MAGIC_NORMAL => {
                let seg = header as *mut Segment;
                let unit = (p as usize - seg as usize) / UNIT_SIZE;
                let first = (*seg).span_of[unit].load(Ordering::Relaxed) as usize;
                Owner::Span(ptr::addr_of_mut!((*seg).spans[first]))
            }
            _ => Owner::Invalid,
        }
    }
}

/// Maps a huge block of `size` bytes aligned to `align` (a power of two).
/// The flag is true if the memory is a fresh (zero-filled) mapping rather
/// than a recycled one.
pub fn alloc_huge(size: usize, align: usize) -> Option<(*mut u8, bool)> {
    let align = align.max(PAGE_SIZE);
    if align > SEGMENT_SIZE {
        return None;
    }
    let data_off = HUGE_HEADER_SIZE.next_multiple_of(align);
    let len = data_off
        .checked_add(size)?
        .checked_next_multiple_of(PAGE_SIZE)?;
    let (base, len, fresh) = match take_cached(len) {
        Some((base, len)) => (base, len, false),
        None => (map_aligned(len)?, len, true),
    };
    // SAFETY: our mapping; the header fits in the first page.
    unsafe {
        let data = base.add(data_off);
        (base as *mut Header).write(Header {
            magic: MAGIC_HUGE,
            map_len: len,
            data,
        });
        Some((data, fresh))
    }
}

/// Usable size of the huge block described by `h`.
///
/// # Safety
/// `h` must be a live huge header.
pub unsafe fn huge_usable_size(h: *const Header) -> usize {
    // SAFETY: caller contract.
    unsafe { (*h).map_len - ((*h).data as usize - h as usize) }
}

/// Start of user data of a huge mapping.
///
/// # Safety
/// `h` must be a live huge header.
pub unsafe fn huge_data(h: *const Header) -> *mut u8 {
    // SAFETY: caller contract.
    unsafe { (*h).data }
}

/// Releases a huge block: into the cache if there is room, else back to
/// the kernel.
///
/// # Safety
/// `h` must be a live huge header that is not used afterwards.
pub unsafe fn free_huge(h: *mut Header) {
    // SAFETY: caller contract.
    let len = unsafe {
        let len = (*h).map_len;
        (*h).magic = 0;
        len
    };
    if len <= HUGE_CACHE_MAX_LEN {
        let mut cache = HUGE_CACHE.lock();
        if cache.count < HUGE_CACHE_SLOTS {
            let n = cache.count;
            cache.entries[n] = (h as usize, len);
            cache.count = n + 1;
            return;
        }
    }
    // SAFETY: our mapping, no longer referenced.
    let _ = unsafe { sys::munmap(h as *mut u8, len) };
}

/// A lock used to serialise allocator-global state around `fork`.
pub fn pool_lock() -> &'static RawMutex {
    POOL.raw()
}

/// The huge-block cache lock, for `fork`.
pub fn huge_cache_lock() -> &'static RawMutex {
    HUGE_CACHE.raw()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn find_run_finds_first_fit() {
        assert_eq!(find_run(u64::MAX, 1), Some(0));
        assert_eq!(find_run(u64::MAX << 3, 1), Some(3));
        assert_eq!(find_run(0b1111_0111, 4), Some(4));
        assert_eq!(find_run(0b0111, 4), None);
        assert_eq!(find_run(0, 1), None);
        assert_eq!(find_run(u64::MAX, 64), Some(0));
    }

    #[test]
    fn spans_and_huge_round_trip() {
        let span = alloc_span(0, 1).unwrap();
        // SAFETY: freshly allocated span.
        unsafe {
            assert_eq!((*span).block_size, 16);
            assert!((*span).capacity > 15000);
            assert_eq!((*span).data as usize % PAGE_SIZE, 0);
            assert!(!(*span).is_allocated(0));
            (*span).mark_allocated(70);
            assert!((*span).is_allocated(70));
            (*span).mark_free(70);
            assert!(!(*span).is_allocated(70));
            (*span).bump = 10;
            assert_eq!((*span).block_index((*span).data.add(32)), Some(2));
            assert_eq!((*span).block_index((*span).data.add(33)), None);
            assert_eq!((*span).block_index((*span).data.add(160)), None);
            match lookup((*span).data) {
                Owner::Span(s) => assert_eq!(s, span),
                _ => panic!("wrong owner"),
            }
            let big = alloc_span(47, 1).unwrap();
            assert_eq!((*big).units, 4);
            assert_eq!((*big).block_size as usize, 128 * 1024);
            assert!((*big).capacity >= 7);
            release_span(big);
            release_span(span);
        }
        let (p, fresh) = alloc_huge(1_000_000, 16).unwrap();
        assert!(fresh);
        // SAFETY: valid huge block.
        unsafe {
            match lookup(p) {
                Owner::Huge(h) => {
                    assert!(huge_usable_size(h) >= 1_000_000);
                    assert_eq!(huge_data(h), p);
                    p.write_bytes(1, 1_000_000);
                    free_huge(h);
                }
                _ => panic!("wrong owner"),
            }
        }
        // The freed mapping is cached and reused for a similar request
        // (unless a concurrently running test took it first).
        let (q, fresh) = alloc_huge(900_000, 16).unwrap();
        if q == p && !fresh {
            // SAFETY: valid huge block; the recycled memory still holds the
            // old bytes, which `alloc_zeroed` is responsible for clearing.
            unsafe { assert_eq!(*q, 1) };
        }
        // SAFETY: valid huge block.
        unsafe {
            match lookup(q) {
                Owner::Huge(h) => free_huge(h),
                _ => panic!("wrong owner"),
            }
        }
        let (p, _) = alloc_huge(10, 1 << 20).unwrap();
        assert_eq!(p as usize % (1 << 20), 0);
        // SAFETY: valid huge block.
        unsafe {
            match lookup(p) {
                Owner::Huge(h) => free_huge(h),
                _ => panic!("wrong owner"),
            }
        }
        assert!(alloc_huge(10, SEGMENT_SIZE * 2).is_none());
    }
}
