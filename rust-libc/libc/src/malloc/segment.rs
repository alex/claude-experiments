//! Segments, spans and huge mappings.
//!
//! All memory handed out by the allocator lives in *segments*: 16 MiB
//! regions aligned to their size, so that the segment of any pointer is
//! found by masking. A segment is either:
//!
//! * a **normal segment**, split into 64 units of 256 KiB. Spans of one,
//!   four or eight consecutive units each serve a single size class, and
//!   a *large span* of any number of units holds a single block bigger
//!   than [`MAX_SMALL`](super::classes::MAX_SMALL) (up to [`LARGE_MAX`]).
//!   The segment header at the start of the segment holds the per-span
//!   metadata, so no metadata is ever adjacent to user data;
//! * a **huge mapping** for a single allocation larger than
//!   [`LARGE_MAX`], with only the small [`Header`] in its first page.
//!
//! Each span starts with an allocation bitmap (one bit per block) followed
//! by the page-aligned block area (a large span keeps its single bit in
//! its metadata). The bitmap makes double and invalid frees detectable.
//!
//! Units freed back to the pool keep their pages: they are returned to
//! the kernel only once the segment has been idle for a while, or when
//! the resident free units exceed a budget, so a program cycling through
//! big buffers (the common case for large blocks) reuses resident memory
//! instead of paying page faults on every allocation.

use super::classes::{CLASS_INV, CLASS_INV_SHIFT, CLASS_SIZE, units_for_class};
use crate::sync::{Mutex, RawMutex};
use crate::sys::{
    self, MAP_ANONYMOUS, MAP_NORESERVE, MAP_PRIVATE, MIN_PAGE_SIZE, PROT_READ, PROT_WRITE,
};
use core::ptr;
use core::sync::atomic::{AtomicU8, AtomicU64, AtomicUsize, Ordering};

/// Size of one unit.
pub const UNIT_SIZE: usize = 256 * 1024;
/// Size (and alignment) of a segment.
pub const SEGMENT_SIZE: usize = 16 * 1024 * 1024;
/// Units per normal segment.
pub const UNITS: usize = SEGMENT_SIZE / UNIT_SIZE;
/// Bytes at the start of a normal segment reserved for the header.
const HEADER_SIZE: usize = 16384;
/// Bytes at the start of a huge mapping reserved for the header.
const HUGE_HEADER_SIZE: usize = MIN_PAGE_SIZE;
/// Largest block served by a large span (unit 0 holds the header, so
/// one unit less than a segment).
pub const LARGE_MAX: usize = (UNITS - 1) * UNIT_SIZE;
/// `Span::class` of a large span (one block, any number of units).
pub const LARGE_CLASS: u8 = u8::MAX;

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
    /// Free units whose pages may still be resident: single-unit spans
    /// are released without returning their pages, because a thread that
    /// comes and goes should not pay a TLB shootdown and a refault for
    /// every span it touched. Once most of a segment is free they are
    /// returned in bulk (see [`release_span`]). Protected by the pool lock.
    resident: u64,
    /// For each unit, the index of the first unit of its span. Only
    /// meaningful for allocated units.
    span_of: [AtomicU8; UNITS],
    /// When units were last freed back (milliseconds); drives the return
    /// of idle pages. Protected by the pool lock.
    idle_since: u64,
    spans: [Span; UNITS],
}

const _: () = assert!(core::mem::size_of::<Segment>() <= HEADER_SIZE);
const _: () = assert!(core::mem::size_of::<Header>() <= HUGE_HEADER_SIZE);

/// Metadata of a span. Lives in the segment header, indexed by the
/// span's first unit.
///
/// Three cache lines: what every thread reads to classify a pointer
/// (constant while the span is live), what the owner updates on every
/// operation, and the remote-free stack that other threads write. Kept
/// apart so a foreign thread freeing a block neither stalls on nor
/// invalidates the owner's hot line.
#[repr(C, align(64))]
pub struct Span {
    // --- read-mostly ---
    /// Block size in bytes; 0 for a span that is not allocated.
    pub block_size: u32,
    /// Size class.
    pub class: u8,
    /// Units in this span.
    pub units: u8,
    _pad0: [u8; 2],
    /// Number of blocks in the block area.
    pub capacity: u32,
    _pad1: [u8; 4],
    /// Allocation bitmap, one bit per block.
    pub bitmap: *mut u64,
    /// Start of the page-aligned block area.
    pub data: *mut u8,
    /// The owning heap, or null when orphaned.
    pub owner: AtomicUsize,
    _pad2: [u8; 24],
    // --- owner-hot ---
    /// Blocks `[bump, capacity)` have never been handed out.
    pub bump: u32,
    /// Blocks currently allocated, as seen by the owning heap (remote
    /// frees are not subtracted until collected).
    pub used: u32,
    /// Blocks `[0, zeroed)` of a never-used bump area are known to be
    /// zero (fresh pages), so `calloc` need not clear them.
    pub zeroed: u32,
    /// True while the span is on its heap's `full` list.
    pub is_full: bool,
    _pad3: [u8; 3],
    /// Head of the local free list, encoded (see `Heap`).
    pub free: usize,
    /// Previous span in the owning heap's per-class list (or orphan list).
    pub prev: *mut Span,
    /// Next span in the owning heap's per-class list (or orphan list).
    pub next: *mut Span,
    /// When the span entered a heap's reserve (milliseconds).
    pub retained_at: u64,
    /// The allocation bitmap of a large span (a single bit), so its
    /// block area needs no bitmap page.
    inline_bits: u64,
    _pad4: [u8; 8],
    // --- written by other threads ---
    /// Head of the lock-free list of blocks freed by other threads.
    pub remote: AtomicUsize,
    _pad5: [u8; 56],
}

const _: () = assert!(core::mem::size_of::<Span>() == 192);

impl Span {
    #[allow(clippy::declare_interior_mutable_const)]
    const EMPTY: Span = Span {
        block_size: 0,
        class: 0,
        units: 0,
        _pad0: [0; 2],
        capacity: 0,
        _pad1: [0; 4],
        bitmap: ptr::null_mut(),
        data: ptr::null_mut(),
        owner: AtomicUsize::new(0),
        _pad2: [0; 24],
        bump: 0,
        used: 0,
        zeroed: 0,
        is_full: false,
        _pad3: [0; 3],
        free: 0,
        prev: ptr::null_mut(),
        next: ptr::null_mut(),
        retained_at: 0,
        inline_bits: 0,
        _pad4: [0; 8],
        remote: AtomicUsize::new(0),
        _pad5: [0; 56],
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
        if self.class == LARGE_CLASS {
            return (off == 0).then_some(0);
        }
        // Division by multiplication (see `CLASS_INV`); the multiply-back
        // check makes the result exact for any `off`, valid or not.
        let idx =
            ((off as u64).wrapping_mul(CLASS_INV[self.class as usize]) >> CLASS_INV_SHIFT) as usize;
        if idx >= self.bump as usize || idx * bs != off {
            None
        } else {
            Some(idx as u32)
        }
    }

    /// Tests the allocation bit of block `idx`.
    ///
    /// # Safety
    /// The span must be live (its bitmap mapped) and `idx < capacity`,
    /// which [`Span::block_index`] guarantees for its results.
    #[inline]
    pub unsafe fn is_allocated(&self, idx: u32) -> bool {
        debug_assert!(idx < self.capacity);
        // SAFETY: caller contract.
        unsafe { *self.bitmap.add(idx as usize / 64) & (1 << (idx % 64)) != 0 }
    }

    /// Sets the allocation bit of block `idx`.
    ///
    /// # Safety
    /// As for [`Span::is_allocated`].
    #[inline]
    pub unsafe fn mark_allocated(&mut self, idx: u32) {
        debug_assert!(idx < self.capacity);
        // SAFETY: caller contract.
        unsafe { *self.bitmap.add(idx as usize / 64) |= 1 << (idx % 64) }
    }

    /// Clears the allocation bit of block `idx`.
    ///
    /// # Safety
    /// As for [`Span::is_allocated`].
    #[inline]
    pub unsafe fn mark_free(&mut self, idx: u32) {
        debug_assert!(idx < self.capacity);
        // SAFETY: caller contract.
        unsafe { *self.bitmap.add(idx as usize / 64) &= !(1 << (idx % 64)) }
    }
}

/// Global pool of normal segments.
struct Pool {
    head: *mut Segment,
    /// Free units across all segments whose pages are still resident.
    resident_free: usize,
    /// Units currently allocated to spans.
    live_units: usize,
    /// When the pool last looked for idle memory to return.
    last_purge: u64,
}

impl Pool {
    /// Resident free units the pool may keep: a floor, or as much as is
    /// allocated when that is more (a program with a big live set
    /// oscillates by bigger amounts, and the decay pass returns what it
    /// stops using).
    fn resident_budget(&self) -> usize {
        self.live_units.max(RESIDENT_FREE_MAX / UNIT_SIZE)
    }
}

/// Floor of the resident free budget, in bytes.
const RESIDENT_FREE_MAX: usize = 64 << 20;

/// A segment's free units go back to the kernel once nothing has been
/// freed into it for this long (checked whenever the pool is used).
const POOL_DECAY_MS: u64 = 250;

/// Over budget, only segments that have been idle for at least this
/// long are swept: one that just had a block freed into it is the most
/// likely to be reused (a program cycling through big buffers frees and
/// reallocates within microseconds), and sweeping it would turn every
/// reuse into page faults. Beyond twice the budget the sweep no longer
/// waits.
const POOL_MIN_IDLE_MS: u64 = 10;

// SAFETY: access is serialised by the mutex.
unsafe impl Send for Pool {}

static POOL: Mutex<Pool> = Mutex::new(Pool {
    head: ptr::null_mut(),
    resident_free: 0,
    live_units: 0,
    last_purge: 0,
});

/// Recently freed huge mappings, kept for reuse so that programs which
/// repeatedly allocate and free large blocks do not pay for `mmap`,
/// `munmap` and the page faults of a fresh mapping every time. Entries
/// keep their contents (like any other freed memory); `calloc` zeroes
/// them explicitly.
struct HugeCache {
    entries: [CachedMapping; HUGE_CACHE_SLOTS],
    count: usize,
    /// Total length of the entries whose pages are still resident.
    resident: usize,
    /// Bytes currently allocated as huge blocks (their mappings).
    live: usize,
}

impl HugeCache {
    /// Resident cache budget: a floor, or as much as the program has
    /// live in huge blocks when that is more (its working set shows it
    /// will reuse that much).
    fn resident_budget(&self) -> usize {
        (self.live * 2).max(HUGE_CACHE_RESIDENT_MIN)
    }
}

#[derive(Clone, Copy)]
struct CachedMapping {
    base: usize,
    len: usize,
    /// False once the pages were returned with `MADV_DONTNEED`.
    resident: bool,
    /// When the mapping was freed (milliseconds, `now_ms`).
    freed_at: u64,
}

/// Resident cached mappings older than this are returned to the kernel
/// the next time the cache is touched: a program that stopped reusing
/// large blocks should not keep them resident, one that churns through
/// them keeps everything warm.
const HUGE_DECAY_MS: u64 = 250;

/// A coarse monotonic clock in milliseconds (a vDSO read).
fn now_ms() -> u64 {
    let t = sys::clock_gettime(sys::CLOCK_MONOTONIC_COARSE).unwrap_or_default();
    t.tv_sec as u64 * 1000 + t.tv_nsec as u64 / 1_000_000
}

/// Returns the pages of resident cached mappings that have been idle
/// for longer than the decay period, and of the least recently freed
/// ones while the resident total exceeds the budget.
fn purge_huge_cache(cache: &mut HugeCache, now: u64) {
    let budget = cache.resident_budget();
    let mut oldest = None;
    for i in 0..cache.count {
        let e = cache.entries[i];
        if !e.resident {
            continue;
        }
        if now.saturating_sub(e.freed_at) > HUGE_DECAY_MS {
            madvise_dontneed(e.base as *mut u8, e.len);
            cache.entries[i].resident = false;
            cache.resident -= e.len;
        } else if oldest.is_none_or(|o: usize| e.freed_at < cache.entries[o].freed_at) {
            oldest = Some(i);
        }
    }
    while cache.resident > budget {
        let Some(i) = oldest else { break };
        let e = cache.entries[i];
        madvise_dontneed(e.base as *mut u8, e.len);
        cache.entries[i].resident = false;
        cache.resident -= e.len;
        oldest = (0..cache.count)
            .filter(|&j| cache.entries[j].resident)
            .min_by_key(|&j| cache.entries[j].freed_at);
    }
}

const HUGE_CACHE_SLOTS: usize = 32;
/// Mappings larger than this always go back to the kernel.
const HUGE_CACHE_MAX_LEN: usize = 64 << 20;

static HUGE_CACHE: Mutex<HugeCache> = Mutex::new(HugeCache {
    entries: [CachedMapping {
        base: 0,
        len: 0,
        resident: false,
        freed_at: 0,
    }; HUGE_CACHE_SLOTS],
    count: 0,
    resident: 0,
    live: 0,
});

/// Cached mappings keep their pages (so reuse costs nothing) up to this
/// many bytes in total; beyond it their pages are returned to the kernel
/// and only the address range is kept, saving the mmap/munmap pair.
const HUGE_CACHE_RESIDENT_MIN: usize = 256 << 20;

/// Takes the smallest cached mapping of at least `len` bytes that does
/// not waste more than half of itself. The flag says whether its pages
/// were returned (so it reads as zeros).
fn take_cached(len: usize) -> Option<(*mut u8, usize, bool)> {
    let mut cache = HUGE_CACHE.lock();
    let now = now_ms();
    purge_huge_cache(&mut cache, now);
    // Best fit among the cached mappings, preferring a resident one (no
    // page faults) over a closer fit. A larger mapping is still used (a
    // fresh one would cost a system call and page faults), but when it
    // is more than twice the request the part beyond the request is
    // returned to the kernel so it does not stay resident for nothing.
    // Below that the excess is kept: trimming costs a system call now
    // and page faults when the mapping is reused for a bigger block,
    // which for a workload cycling through large blocks of varying size
    // is most of the cost of every allocation.
    // Ranking: a mapping within twice the request ("good fit") beats one
    // that would need trimming; among good fits a resident one, then the
    // smallest; among oversized ones a non-resident one (its excess costs
    // nothing as it is), then the smallest.
    let mut best: Option<usize> = None;
    for i in 0..cache.count {
        let e = cache.entries[i];
        if e.len < len {
            continue;
        }
        let better = match best {
            None => true,
            Some(b) => {
                let c = cache.entries[b];
                let (ge, gc) = (e.len <= len * 2, c.len <= len * 2);
                if ge != gc {
                    ge
                } else if e.resident != c.resident {
                    e.resident == ge
                } else {
                    e.len < c.len
                }
            }
        };
        if better {
            best = Some(i);
        }
    }
    let i = best?;
    let entry = cache.entries[i];
    cache.count -= 1;
    cache.entries[i] = cache.entries[cache.count];
    if entry.resident {
        cache.resident -= entry.len;
        let keep = len.next_multiple_of(sys::page_size());
        if entry.len > keep * 2 {
            madvise_dontneed((entry.base + keep) as *mut u8, entry.len - keep);
        }
    }
    cache.live += entry.len;
    Some((entry.base as *mut u8, entry.len, !entry.resident))
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
        ptr::addr_of_mut!((*seg).resident).write(0);
        ptr::addr_of_mut!((*seg).idle_since).write(0);
        for i in 0..UNITS {
            ptr::addr_of_mut!((*seg).span_of[i]).write(AtomicU8::new(0));
            ptr::addr_of_mut!((*seg).spans[i]).write(Span::EMPTY);
        }
    }
    if !register(seg as usize) {
        // SAFETY: our own fresh mapping, not yet linked anywhere.
        let _ = unsafe { sys::munmap(seg as *mut u8, SEGMENT_SIZE) };
        return None;
    }
    Some(seg)
}

/// Finds `n` consecutive free units in `free`, returning the first index.
fn find_run(free: u64, n: usize) -> Option<usize> {
    let mask = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
    (0..=UNITS - n).find(|&i| free & (mask << i) == mask << i)
}

/// Mask of units `first..first + units`.
fn run_mask(first: usize, units: usize) -> u64 {
    if units >= UNITS {
        u64::MAX
    } else {
        ((1u64 << units) - 1) << first
    }
}

/// Finds `units` consecutive free units, mapping a new segment if none
/// has them. Unit 0 (which starts with the segment header) is skipped
/// when `skip_header` is set. Idle memory is returned first.
fn take_units(pool: &mut Pool, units: usize, skip_header: bool) -> Option<(*mut Segment, usize)> {
    // SAFETY: the pool lock is held.
    unsafe { purge(pool, now_ms()) };
    let mut seg = pool.head;
    loop {
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
        let mut free = unsafe { (*seg).free_units };
        if skip_header {
            free &= !1;
        }
        if let Some(first) = find_run(free, units) {
            return Some((seg, first));
        }
        // SAFETY: as above.
        seg = unsafe { (*seg).next };
    }
}

/// Takes free units `start..start + units` of `seg` for the span whose
/// first unit is `first`. Returns whether any of them may hold old data
/// (pages returned to the kernel, or never touched, read as zeros).
///
/// # Safety
/// The pool lock must be held and the units must be free.
unsafe fn claim_units(
    pool: &mut Pool,
    seg: *mut Segment,
    start: usize,
    units: usize,
    first: usize,
) -> bool {
    let mask = run_mask(start, units);
    // SAFETY: caller contract.
    unsafe {
        let dirty = (*seg).resident & mask != 0;
        pool.resident_free -= ((*seg).resident & mask).count_ones() as usize;
        pool.live_units += units;
        (*seg).free_units &= !mask;
        (*seg).resident &= !mask;
        for u in start..start + units {
            (*seg).span_of[u].store(first as u8, Ordering::Relaxed);
        }
        dirty
    }
}

/// Allocates and initialises a span for `class`, owned by `owner`.
pub fn alloc_span(class: usize, owner: usize) -> Option<*mut Span> {
    let units = units_for_class(class);
    let mut pool = POOL.lock();
    let (seg, first) = take_units(&mut pool, units, false)?;
    // SAFETY: the units were free and are now ours; all writes are to the
    // header (under the pool lock) or to the span's own memory.
    unsafe {
        let dirty = claim_units(&mut pool, seg, first, units, first);
        let span = ptr::addr_of_mut!((*seg).spans[first]);
        span.write(Span::EMPTY);
        (*span).units = units as u8;
        (*span).owner.store(owner, Ordering::Relaxed);
        init_span(span, seg, first, class, !dirty);
        Some(span)
    }
}

/// Allocates a large span holding one block of at least `size` bytes
/// (up to [`LARGE_MAX`]). Returns the block and whether it is known to
/// be zero-filled.
pub fn alloc_large(size: usize) -> Option<(*mut u8, bool)> {
    let units = size.div_ceil(UNIT_SIZE).max(1);
    if units > UNITS - 1 {
        return None;
    }
    let mut pool = POOL.lock();
    let (seg, first) = take_units(&mut pool, units, true)?;
    // SAFETY: as in `alloc_span`.
    unsafe {
        let dirty = claim_units(&mut pool, seg, first, units, first);
        let span = ptr::addr_of_mut!((*seg).spans[first]);
        span.write(Span::EMPTY);
        (*span).units = units as u8;
        (*span).class = LARGE_CLASS;
        (*span).block_size = (units * UNIT_SIZE) as u32;
        (*span).capacity = 1;
        (*span).bump = 1;
        (*span).used = 1;
        (*span).inline_bits = 1;
        (*span).bitmap = ptr::addr_of_mut!((*span).inline_bits);
        (*span).data = (seg as usize + first * UNIT_SIZE) as *mut u8;
        Some(((*span).data, !dirty))
    }
}

/// Frees the block `p` of the large span `span`. The checks are redone
/// under the pool lock, so two threads freeing the same block cannot
/// both get through.
///
/// # Safety
/// `span` must be a span of a live segment.
pub unsafe fn free_large(span: *mut Span, p: *mut u8) {
    let mut pool = POOL.lock();
    // SAFETY: caller contract; the pool lock protects the metadata.
    unsafe {
        if (*span).class != LARGE_CLASS || (*span).data != p || (*span).inline_bits != 1 {
            super::corrupt("double free of a large block");
        }
        (*span).inline_bits = 0;
        (*span).used = 0;
        release_locked(&mut pool, span, now_ms());
    }
}

/// Resizes the large span `span` in place to hold `size` bytes: shrinks
/// by giving back its tail units, grows into free units right after it.
/// Returns false if that is not possible (the caller then moves the
/// block).
///
/// # Safety
/// `span` must be a live large span.
pub unsafe fn resize_large(span: *mut Span, size: usize) -> bool {
    let want = size.div_ceil(UNIT_SIZE).max(1);
    if want > UNITS - 1 {
        return false;
    }
    let seg = segment_of(span as *const u8) as *mut Segment;
    // SAFETY: `span` lives in `seg`'s header.
    let first = unsafe {
        (span as usize - ptr::addr_of!((*seg).spans) as usize) / core::mem::size_of::<Span>()
    };
    let mut pool = POOL.lock();
    // SAFETY: caller contract; the pool lock protects the bookkeeping.
    unsafe {
        let have = (*span).units as usize;
        if want < have {
            let n = have - want;
            let mask = run_mask(first + want, n);
            (*seg).free_units |= mask;
            (*seg).resident |= mask;
            pool.resident_free += n;
            pool.live_units -= n;
            let now = now_ms();
            (*seg).idle_since = now;
            purge(&mut pool, now);
        } else if want > have {
            let n = want - have;
            if first + want > UNITS {
                return false;
            }
            let mask = run_mask(first + have, n);
            if (*seg).free_units & mask != mask {
                return false;
            }
            claim_units(&mut pool, seg, first + have, n, first);
        }
        (*span).units = want as u8;
        (*span).block_size = (want * UNIT_SIZE) as u32;
    }
    true
}

/// Lays out `span` (first unit `first` of `seg`, `units` set) for
/// `class`: bitmap first, then the page-aligned block area. `zeroed`
/// says whether the block area is known to be all zeros.
///
/// # Safety
/// The span must be empty (no live blocks) and owned by the caller.
unsafe fn init_span(span: *mut Span, seg: *mut Segment, first: usize, class: usize, zeroed: bool) {
    // SAFETY: caller contract.
    unsafe {
        let units = (*span).units as usize;
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
        let data = (start + bitmap_bytes).next_multiple_of(MIN_PAGE_SIZE);
        let capacity = ((end - data) / block_size) as u32;
        ptr::write_bytes(start as *mut u8, 0, bitmap_bytes);
        (*span).block_size = block_size as u32;
        (*span).class = class as u8;
        (*span).is_full = false;
        (*span).capacity = capacity;
        (*span).bump = 0;
        (*span).used = 0;
        (*span).free = 0;
        (*span).zeroed = if zeroed { capacity } else { 0 };
        (*span).remote.store(0, Ordering::Relaxed);
        (*span).prev = ptr::null_mut();
        (*span).next = ptr::null_mut();
        (*span).bitmap = start as *mut u64;
        (*span).data = data as *mut u8;
    }
}

/// Re-purposes an empty span for `class`, which must use the same number
/// of units. Its blocks are handed out from the start again, sequentially.
///
/// # Safety
/// `span` must be empty (every block freed, remote frees collected) and
/// owned by the caller.
pub unsafe fn reinit_span(span: *mut Span, class: usize) {
    let seg = segment_of(span as *const u8) as *mut Segment;
    // SAFETY: `span` lives in `seg`'s header.
    let first = unsafe {
        (span as usize - ptr::addr_of!((*seg).spans) as usize) / core::mem::size_of::<Span>()
    };
    // SAFETY: caller contract.
    debug_assert_eq!(units_for_class(class), unsafe { (*span).units } as usize);
    // SAFETY: caller contract; the old block area may hold old data.
    unsafe { init_span(span, seg, first, class, false) };
}

/// Returns a completely free span's units to its segment. The pages stay
/// resident until [`purge`] decides otherwise.
///
/// # Safety
/// `span` must be an allocated span no heap references any more.
pub unsafe fn release_span(span: *mut Span) {
    let mut pool = POOL.lock();
    let now = now_ms();
    // SAFETY: caller contract.
    unsafe { release_locked(&mut pool, span, now) }
}

/// [`release_span`] for a span that has already sat unused in a heap's
/// reserve since `idle_since` (milliseconds): its segment counts as idle
/// from then, so the pages go back right away rather than after another
/// decay period.
///
/// # Safety
/// As for [`release_span`].
pub unsafe fn release_idle_span(span: *mut Span, idle_since: u64) {
    let mut pool = POOL.lock();
    // SAFETY: caller contract.
    unsafe { release_locked(&mut pool, span, idle_since) }
}

/// [`release_span`] with the pool lock held; `idle_since` is when the
/// span's memory was last in use.
///
/// # Safety
/// As for [`release_span`].
unsafe fn release_locked(pool: &mut Pool, span: *mut Span, idle_since: u64) {
    let seg = segment_of(span as *const u8) as *mut Segment;
    // SAFETY: `span` lives in `seg`'s header; the pool lock protects the
    // segment's unit bookkeeping.
    unsafe {
        let first =
            (span as usize - ptr::addr_of!((*seg).spans) as usize) / core::mem::size_of::<Span>();
        let units = (*span).units as usize;
        // Poison the metadata so a stale free into this span is caught.
        (*span).block_size = 0;
        (*span).capacity = 0;
        (*span).bump = 0;
        (*span).class = 0;
        (*span).owner.store(0, Ordering::Relaxed);
        let mask = run_mask(first, units);
        (*seg).free_units |= mask;
        pool.live_units -= units;
        let now = now_ms();
        if now.saturating_sub(idle_since) >= POOL_DECAY_MS {
            // Already idle for a whole decay period (a span from a
            // heap's reserve): return the pages right away instead of
            // waiting for the next decay pass, which runs only once per
            // period and would leave the rest of a decaying reserve
            // resident.
            madvise_units(seg, first, units);
        } else {
            (*seg).resident |= mask;
            pool.resident_free += units;
            (*seg).idle_since = (*seg).idle_since.max(idle_since);
        }
        purge(pool, now);
    }
}

/// Returns idle memory to the kernel: the resident free units of every
/// segment that has had nothing freed into it for [`POOL_DECAY_MS`]
/// (an entirely free segment is unmapped, unless it is the last one),
/// and, while the resident free units exceed the pool's budget, those
/// of the least recently used segments. The decay pass runs at most
/// once per decay period.
///
/// # Safety
/// The pool lock must be held.
unsafe fn purge(pool: &mut Pool, now: u64) {
    let budget = pool.resident_budget();
    if now.saturating_sub(pool.last_purge) >= POOL_DECAY_MS {
        pool.last_purge = now;
        let mut link = &mut pool.head as *mut *mut Segment;
        // SAFETY: caller contract; segments in the pool are valid.
        unsafe {
            while !(*link).is_null() {
                let s = *link;
                if now.saturating_sub((*s).idle_since) >= POOL_DECAY_MS {
                    let last = pool.head == s && (*s).next.is_null();
                    if (*s).free_units == u64::MAX && !last {
                        pool.resident_free -= (*s).resident.count_ones() as usize;
                        *link = (*s).next;
                        unregister(s as usize);
                        let _ = sys::munmap(s as *mut u8, SEGMENT_SIZE);
                        continue;
                    }
                    if (*s).resident != 0 {
                        pool.resident_free -= (*s).resident.count_ones() as usize;
                        sweep_segment(s);
                    }
                }
                link = ptr::addr_of_mut!((*s).next);
            }
        }
    }
    while pool.resident_free > budget {
        let mut victim: *mut Segment = ptr::null_mut();
        let mut s = pool.head;
        // SAFETY: as above.
        unsafe {
            while !s.is_null() {
                if (*s).resident != 0
                    && (victim.is_null() || (*s).idle_since < (*victim).idle_since)
                {
                    victim = s;
                }
                s = (*s).next;
            }
            if victim.is_null()
                || (now.saturating_sub((*victim).idle_since) < POOL_MIN_IDLE_MS
                    && pool.resident_free <= budget * 2)
            {
                break;
            }
            pool.resident_free -= (*victim).resident.count_ones() as usize;
            sweep_segment(victim);
        }
    }
}

/// Returns the pages of every resident free unit of `seg`.
///
/// # Safety
/// The pool lock must be held.
unsafe fn sweep_segment(seg: *mut Segment) {
    // SAFETY: caller contract.
    unsafe {
        let mut bits = (*seg).resident;
        while bits != 0 {
            let start = bits.trailing_zeros() as usize;
            let run = (bits >> start).trailing_ones() as usize;
            madvise_units(seg, start, run);
            bits &= !run_mask(start, run);
        }
        (*seg).resident = 0;
    }
}

/// Lets the kernel reclaim the pages of units `first..first + n` (they
/// read as zeros if reused). The segment header at the start of unit 0
/// is kept.
///
/// # Safety
/// The units must be free.
unsafe fn madvise_units(seg: *mut Segment, first: usize, n: usize) {
    let mut start = seg as usize + first * UNIT_SIZE;
    let end = start + n * UNIT_SIZE;
    if first == 0 {
        // Keep the header, rounded to the kernel's page size (which may
        // exceed the header's size).
        start += HEADER_SIZE.next_multiple_of(sys::page_size());
    }
    if end > start {
        madvise_dontneed(start as *mut u8, end - start);
    }
}

/// The coarse clock, for the heaps' span reserves.
pub fn coarse_ms() -> u64 {
    now_ms()
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

/// The span whose units contain `p`, for pointers known to lie in a
/// live normal segment (no registry check).
///
/// # Safety
/// `p` must point into a unit of a live span.
pub unsafe fn span_containing(p: *const u8) -> *mut Span {
    let seg = segment_of(p) as *mut Segment;
    // SAFETY: caller contract.
    unsafe {
        let unit = (p as usize - seg as usize) / UNIT_SIZE;
        let first = (*seg).span_of[unit].load(Ordering::Relaxed) as usize;
        ptr::addr_of_mut!((*seg).spans[first])
    }
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

/// Classifies `p`. The header is only read after the registry confirms
/// that a live mapping of ours starts there, so a foreign pointer, an
/// already unmapped block or an interior pointer of a huge block is
/// `Invalid` rather than a misread header.
pub fn lookup(p: *mut u8) -> Owner {
    let header = segment_of(p);
    if !is_registered(header as usize) {
        return Owner::Invalid;
    }
    // SAFETY: the registry says a mapping of ours with a header lives
    // there; registration happens after the header is written and
    // unregistration before the mapping is released (both under the
    // respective locks), and the atomics order those writes.
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

// ---------------------------------------------------------------------
// Registry of live mappings.

/// One bit per possible 16 MiB-aligned mapping base in the 48-bit
/// address space (2 MiB of `.bss`, of which only the pages for bases in
/// use are ever touched). [`lookup`] consults it before reading a
/// header, so a pointer that never came from this allocator, or that
/// points into the middle of a huge block (whose interior 16 MiB
/// boundaries hold user data), is reported invalid instead of having its
/// "header" interpreted.
const REGISTRY_WORDS: usize = (1 << 48) / SEGMENT_SIZE / 64;
static REGISTRY: [AtomicU64; REGISTRY_WORDS] = [const { AtomicU64::new(0) }; REGISTRY_WORDS];

fn registry_slot(base: usize) -> Option<(&'static AtomicU64, u64)> {
    let idx = base / SEGMENT_SIZE;
    Some((REGISTRY.get(idx / 64)?, 1 << (idx % 64)))
}

/// Records a new live mapping at `base`. Fails only for addresses above
/// the 48-bit space, which the kernel does not hand out without a hint.
fn register(base: usize) -> bool {
    match registry_slot(base) {
        Some((word, bit)) => {
            word.fetch_or(bit, Ordering::Release);
            true
        }
        None => false,
    }
}

fn unregister(base: usize) {
    if let Some((word, bit)) = registry_slot(base) {
        word.fetch_and(!bit, Ordering::Release);
    }
}

fn is_registered(base: usize) -> bool {
    registry_slot(base).is_some_and(|(word, bit)| word.load(Ordering::Acquire) & bit != 0)
}

/// Maps a huge block of `size` bytes aligned to `align` (a power of two).
/// The flag is true if the memory is a fresh (zero-filled) mapping rather
/// than a recycled one.
pub fn alloc_huge(size: usize, align: usize) -> Option<(*mut u8, bool)> {
    let align = align.max(MIN_PAGE_SIZE);
    if align > SEGMENT_SIZE {
        return None;
    }
    let data_off = HUGE_HEADER_SIZE.next_multiple_of(align);
    let len = data_off
        .checked_add(size)?
        .checked_next_multiple_of(MIN_PAGE_SIZE)?;
    let (base, len, fresh) = match take_cached(len) {
        Some((base, len, zeroed)) => (base, len, zeroed),
        None => {
            let base = map_aligned(len)?;
            HUGE_CACHE.lock().live += len;
            (base, len, true)
        }
    };
    // SAFETY: our mapping; the header fits in the first page.
    let data = unsafe {
        let data = base.add(data_off);
        (base as *mut Header).write(Header {
            magic: MAGIC_HUGE,
            map_len: len,
            data,
        });
        data
    };
    if !register(base as usize) {
        // SAFETY: our own mapping, not yet handed out.
        let _ = unsafe { sys::munmap(base, len) };
        return None;
    }
    Some((data, fresh))
}

/// Resizes the huge block described by `h` to `size` bytes in place or
/// by moving its pages with `mremap`, never by copying. Returns the new
/// data pointer, or `None` if the kernel could not do it (the caller
/// then falls back to allocate-copy-free).
///
/// # Safety
/// `h` must be a live huge header.
pub unsafe fn realloc_huge(h: *mut Header, size: usize) -> Option<*mut u8> {
    // SAFETY: caller contract.
    let (old_len, data_off) = unsafe { ((*h).map_len, (*h).data as usize - h as usize) };
    let new_len = data_off
        .checked_add(size)?
        .checked_next_multiple_of(MIN_PAGE_SIZE)?;
    if new_len == old_len {
        // SAFETY: caller contract.
        return Some(unsafe { (*h).data });
    }
    const MREMAP_MAYMOVE: usize = 1;
    const MREMAP_FIXED: usize = 2;
    // Shrinking, or growing into free space right after the mapping,
    // keeps the (16 MiB aligned) base.
    // SAFETY: our own mapping.
    let r = unsafe {
        crate::arch::syscall5(crate::arch::nr::MREMAP, h as usize, old_len, new_len, 0, 0)
    };
    let base = match sys::check(r) {
        Ok(_) => h as usize,
        Err(_) if new_len < old_len => return None,
        Err(_) => {
            // Move the pages into a fresh aligned reservation: MREMAP_FIXED
            // replaces whatever is mapped at the destination.
            let dest = map_aligned(new_len)? as usize;
            // SAFETY: both ranges are our own mappings.
            let r = unsafe {
                crate::arch::syscall5(
                    crate::arch::nr::MREMAP,
                    h as usize,
                    old_len,
                    new_len,
                    MREMAP_MAYMOVE | MREMAP_FIXED,
                    dest,
                )
            };
            if sys::check(r).is_err() {
                // SAFETY: the reservation is ours and unused.
                let _ = unsafe { sys::munmap(dest as *mut u8, new_len) };
                return None;
            }
            unregister(h as usize);
            dest
        }
    };
    let nh = base as *mut Header;
    // SAFETY: the header moved with its pages (or stayed); the registry
    // entry is refreshed before the block is handed back.
    unsafe {
        (*nh).map_len = new_len;
        (*nh).data = (base + data_off) as *mut u8;
    }
    if !register(base) {
        // SAFETY: our mapping, no longer usable by the caller.
        let _ = unsafe { sys::munmap(nh as *mut u8, new_len) };
        return None;
    }
    // SAFETY: as above.
    Some(unsafe { (*nh).data })
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
    unregister(h as usize);
    let mut cache = HUGE_CACHE.lock();
    cache.live = cache.live.saturating_sub(len);
    let now = now_ms();
    if len <= HUGE_CACHE_MAX_LEN {
        if cache.count == HUGE_CACHE_SLOTS {
            // Full: drop the entry that has been idle longest.
            if let Some(i) = (0..cache.count).min_by_key(|&j| cache.entries[j].freed_at) {
                let e = cache.entries[i];
                if e.resident {
                    cache.resident -= e.len;
                }
                // SAFETY: our mapping, no longer referenced.
                let _ = unsafe { sys::munmap(e.base as *mut u8, e.len) };
                cache.count -= 1;
                cache.entries[i] = cache.entries[cache.count];
            }
        }
        if cache.count < HUGE_CACHE_SLOTS {
            let n = cache.count;
            cache.entries[n] = CachedMapping {
                base: h as usize,
                len,
                resident: true,
                freed_at: now,
            };
            cache.count = n + 1;
            cache.resident += len;
            purge_huge_cache(&mut cache, now);
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
            assert_eq!((*span).data as usize % MIN_PAGE_SIZE, 0);
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
        let (p, _fresh) = alloc_huge(1_000_000, 16).unwrap();
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
