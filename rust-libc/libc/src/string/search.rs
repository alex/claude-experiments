//! SIMD kernels for searching and comparing bytes.
//!
//! Every kernel is generic over the vector type `L` and instantiated by
//! [`dispatch_fn!`](crate::string::simd::dispatch_fn). Two kinds of loads are
//! used:
//!
//! * in-bounds vector loads for length-delimited data (`memchr`,
//!   `memcmp`) whenever a whole vector fits;
//! * "over-reads" of readable memory for the remaining cases: whole
//!   vectors from vector-aligned addresses for NUL-terminated strings
//!   (`strlen`, `strchr`), and for short length-delimited inputs either
//!   an unaligned vector that provably stays inside the current page or
//!   the aligned vector containing the data. An aligned vector never
//!   crosses a page boundary, so if any byte of it is inside the string
//!   or buffer, the whole load is backed by readable memory. This is the
//!   standard technique used by every libc and by Rust's own
//!   `compiler_builtins`; the bytes outside the input are masked off
//!   and never influence the result.
//!
//! For two-string kernels (`strcmp`) whose pointers have different
//! alignments the loads are unaligned instead, and only performed when
//! they provably stay inside the current page.
//!
//! The main loops handle four vectors per iteration, combining the
//! per-vector predicates with cheap vector operations and testing once.

use crate::string::lanes::{Lanes, Mask};
use crate::string::simd::dispatch_fn;
use crate::sys::MIN_PAGE_SIZE;
use core::ffi::c_int;

/// Loads one vector from `p`.
///
/// # Safety
/// `p` must be valid for reads of `L::N` bytes in the sense described in
/// the module documentation.
#[inline(always)]
unsafe fn load<L: Lanes>(p: *const u8) -> L {
    // SAFETY: caller guarantees readability.
    unsafe { L::load(p) }
}

/// True if a read of `n` bytes at `p` stays inside one page.
#[inline(always)]
fn page_safe(p: *const u8, n: usize) -> bool {
    (p as usize & (MIN_PAGE_SIZE - 1)) <= MIN_PAGE_SIZE - n
}

/// [`page_safe`] for two pointers, evaluated without branches.
#[inline(always)]
fn both_page_safe(a: *const u8, b: *const u8, n: usize) -> bool {
    let (oa, ob) = (
        a as usize & (MIN_PAGE_SIZE - 1),
        b as usize & (MIN_PAGE_SIZE - 1),
    );
    oa.max(ob) <= MIN_PAGE_SIZE - n
}

/// Mask of the low `k` bits (all bits for `k >= 64`).
#[inline(always)]
fn low_bits(k: usize) -> u64 {
    if k >= 64 { u64::MAX } else { (1u64 << k) - 1 }
}

/// Finds the bytes equal to `needle` among the `len < L::N` bytes at
/// `p` without a scalar loop, by over-reading as described in the module
/// documentation. Returns a bitmask with bit `i` set when byte `i`
/// matches; bits at or above `len` are clear.
///
/// (Kernels must not use closures: a closure does not inherit the
/// caller's target features, so the SIMD operations inside it would
/// become out-of-line calls.)
///
/// # Safety
/// `p` must be valid for `len` bytes.
#[inline(always)]
unsafe fn small_eq_mask<L: Lanes>(p: *const u8, len: usize, needle: L) -> u64 {
    let n = L::N;
    debug_assert!(len < n);
    if page_safe(p, n) {
        // SAFETY: an unaligned vector that stays inside the page of `p`,
        // whose first byte is inside the buffer.
        return unsafe { load::<L>(p) }.eq(needle).bits() & low_bits(len);
    }
    // `p` lies in the last `n - 1` bytes of its page, so the aligned
    // vector containing it is the last one of the page.
    let a = (p as usize & !(n - 1)) as *const u8;
    let shift = p as usize - a as usize;
    let covered = n - shift;
    // SAFETY: aligned over-read containing byte 0 of the buffer.
    let m = (unsafe { load::<L>(a) }.eq(needle).bits() >> shift) & low_bits(len.min(covered));
    if len <= covered {
        return m;
    }
    // The rest of the buffer starts exactly at the next page.
    // SAFETY: page-aligned vector whose first byte is inside the buffer.
    let rest = unsafe { load::<L>(p.add(covered)) }.eq(needle).bits() & low_bits(len - covered);
    m | (rest << covered)
}

// ---------------------------------------------------------------------
// memchr / memrchr

#[inline(always)]
fn memchr_k<L: Lanes>(hay: &[u8], needle: u8) -> Option<usize> {
    let n = L::N;
    let len = hay.len();
    let p = hay.as_ptr();
    let v = L::splat(needle);
    if len < n {
        if len == 0 {
            return None;
        }
        // SAFETY: `hay` is valid for `len` bytes.
        let m = unsafe { small_eq_mask::<L>(p, len, v) };
        return (m != 0).then(|| m.trailing_zeros() as usize);
    }
    let mut i = 0;
    while i + 4 * n <= len {
        // SAFETY: all four vectors are inside `hay`.
        let (a, b, c, d) = unsafe {
            (
                load::<L>(p.add(i)),
                load::<L>(p.add(i + n)),
                load::<L>(p.add(i + 2 * n)),
                load::<L>(p.add(i + 3 * n)),
            )
        };
        let (ma, mb, mc, md) = (a.eq(v), b.eq(v), c.eq(v), d.eq(v));
        if ma.or(mb).or(mc).or(md).any() {
            let (x, y, z, w) = (ma.bits(), mb.bits(), mc.bits(), md.bits());
            let k = if x != 0 {
                x.trailing_zeros() as usize
            } else if y != 0 {
                n + y.trailing_zeros() as usize
            } else if z != 0 {
                2 * n + z.trailing_zeros() as usize
            } else {
                3 * n + w.trailing_zeros() as usize
            };
            return Some(i + k);
        }
        i += 4 * n;
    }
    while i + n <= len {
        // SAFETY: inside `hay`.
        let m = unsafe { load::<L>(p.add(i)) }.eq(v).bits();
        if m != 0 {
            return Some(i + m.trailing_zeros() as usize);
        }
        i += n;
    }
    if i < len {
        // Overlapping final vector; bytes before `i` were already checked.
        let start = len - n;
        // SAFETY: inside `hay`.
        let m = unsafe { load::<L>(p.add(start)) }.eq(v).bits() & !low_bits(i - start);
        if m != 0 {
            return Some(start + m.trailing_zeros() as usize);
        }
    }
    None
}

dispatch_fn! {
    /// Index of the first `needle` in `hay`.
    pub fn memchr(hay: &[u8], needle: u8) -> Option<usize> = memchr_k;
}

/// Index of the highest set bit.
#[inline(always)]
fn high_bit(m: u64) -> usize {
    63 - m.leading_zeros() as usize
}

#[inline(always)]
fn memrchr_k<L: Lanes>(hay: &[u8], needle: u8) -> Option<usize> {
    let n = L::N;
    let len = hay.len();
    let p = hay.as_ptr();
    let v = L::splat(needle);
    if len < n {
        if len == 0 {
            return None;
        }
        // SAFETY: `hay` is valid for `len` bytes.
        let m = unsafe { small_eq_mask::<L>(p, len, v) };
        return (m != 0).then(|| high_bit(m));
    }
    let mut end = len;
    while end >= 4 * n {
        let base = end - 4 * n;
        // SAFETY: all four vectors are inside `hay`.
        let (a, b, c, d) = unsafe {
            (
                load::<L>(p.add(base)),
                load::<L>(p.add(base + n)),
                load::<L>(p.add(base + 2 * n)),
                load::<L>(p.add(base + 3 * n)),
            )
        };
        let (ma, mb, mc, md) = (a.eq(v), b.eq(v), c.eq(v), d.eq(v));
        if ma.or(mb).or(mc).or(md).any() {
            let (x, y, z, w) = (ma.bits(), mb.bits(), mc.bits(), md.bits());
            let k = if w != 0 {
                3 * n + high_bit(w)
            } else if z != 0 {
                2 * n + high_bit(z)
            } else if y != 0 {
                n + high_bit(y)
            } else {
                high_bit(x)
            };
            return Some(base + k);
        }
        end = base;
    }
    while end >= n {
        // SAFETY: inside `hay`.
        let m = unsafe { load::<L>(p.add(end - n)) }.eq(v).bits();
        if m != 0 {
            return Some(end - n + high_bit(m));
        }
        end -= n;
    }
    if end > 0 {
        // Overlapping first vector; bytes at or after `end` were checked.
        // SAFETY: `len >= n`.
        let m = unsafe { load::<L>(p) }.eq(v).bits() & low_bits(end);
        if m != 0 {
            return Some(high_bit(m));
        }
    }
    None
}

dispatch_fn! {
    /// Index of the last `needle` in `hay`.
    pub fn memrchr(hay: &[u8], needle: u8) -> Option<usize> = memrchr_k;
}

/// [`memchr_k`] returning a pointer, for the C entry point (so that it
/// is a tail call).
///
/// # Safety
/// `s` must be valid for `n` bytes.
#[inline(always)]
unsafe fn memchr_ptr_k<L: Lanes>(s: *const u8, c: u8, n: usize) -> *mut u8 {
    // SAFETY: caller contract.
    let hay = unsafe { core::slice::from_raw_parts(s, n) };
    match memchr_k::<L>(hay, c) {
        // SAFETY: `i < n`.
        Some(i) => unsafe { s.add(i) as *mut u8 },
        None => core::ptr::null_mut(),
    }
}

dispatch_fn! {
    /// `memchr(3)` proper: a pointer to the first `c`, or null.
    ///
    /// # Safety
    /// `s` must be valid for `n` bytes.
    pub unsafe fn memchr_ptr(s: *const u8, c: u8, n: usize) -> *mut u8 = memchr_ptr_k;
}

// ---------------------------------------------------------------------
// strlen / strnlen / strchrnul

/// Vector with a zero byte wherever `v` has a NUL or (when `with_needle`)
/// the needle byte: `min(v, v ^ needle)`. This lets four vectors be
/// combined with three `min`s and tested once.
#[inline(always)]
fn zmin<L: Lanes>(v: L, nd: L, with_needle: bool) -> L {
    if with_needle { v.min(v.xor(nd)) } else { v }
}

/// Scans forward from `s` for the first byte that is NUL (or, if
/// `needle` is `Some`, NUL or the needle) and returns its offset.
///
/// # Safety
/// `s` must point to a NUL-terminated string, or be readable for `limit`
/// bytes.
#[inline(always)]
unsafe fn scan_k<L: Lanes>(s: *const u8, needle: Option<u8>, limit: usize) -> usize {
    let n = L::N;
    let start = s as usize;
    let zero = L::splat(0);
    let nd = L::splat(needle.unwrap_or(0));
    let wn = needle.is_some();
    if limit == 0 {
        return 0;
    }

    // First vector: aligned, with the bytes before `start` ignored.
    let mut p = start & !(n - 1);
    // SAFETY: aligned over-read, see the module documentation.
    let v = unsafe { load::<L>(p as *const u8) };
    let m = zmin::<L>(v, nd, wn).eq(zero).bits() >> (start - p);
    if m != 0 {
        return (m.trailing_zeros() as usize).min(limit);
    }
    p += n;
    loop {
        if p - start >= limit {
            return limit;
        }
        // Four vectors at a time once aligned to a 4-vector block, as
        // long as the first byte of the last vector is inside the limit
        // (so every byte of the block is readable or past a NUL).
        if p & (4 * n - 1) == 0 && limit - (p - start) > 3 * n {
            // SAFETY: as above; the previous vectors contained no NUL.
            let (a, b, c, d) = unsafe {
                (
                    load::<L>(p as *const u8),
                    load::<L>((p + n) as *const u8),
                    load::<L>((p + 2 * n) as *const u8),
                    load::<L>((p + 3 * n) as *const u8),
                )
            };
            let (za, zb, zc, zd) = (
                zmin::<L>(a, nd, wn),
                zmin::<L>(b, nd, wn),
                zmin::<L>(c, nd, wn),
                zmin::<L>(d, nd, wn),
            );
            if za.min(zb).min(zc.min(zd)).eq(zero).any() {
                let x = za.eq(zero).bits();
                let y = zb.eq(zero).bits();
                let z = zc.eq(zero).bits();
                let w = zd.eq(zero).bits();
                let k = if x != 0 {
                    x.trailing_zeros() as usize
                } else if y != 0 {
                    n + y.trailing_zeros() as usize
                } else if z != 0 {
                    2 * n + z.trailing_zeros() as usize
                } else {
                    3 * n + w.trailing_zeros() as usize
                };
                return (p - start + k).min(limit);
            }
            p += 4 * n;
            continue;
        }
        // SAFETY: as above.
        let v = unsafe { load::<L>(p as *const u8) };
        let m = zmin::<L>(v, nd, wn).eq(zero).bits();
        if m != 0 {
            return (p - start + m.trailing_zeros() as usize).min(limit);
        }
        p += n;
    }
}

/// [`scan_k`] for `strlen`.
///
/// # Safety
/// `s` must point to a NUL-terminated string.
#[inline(always)]
unsafe fn strlen_k<L: Lanes>(s: *const u8) -> usize {
    // SAFETY: forwarded.
    unsafe { scan_k::<L>(s, None, usize::MAX) }
}

/// [`scan_k`] for `strnlen`.
///
/// # Safety
/// `s` must be readable up to the NUL terminator or `max` bytes.
#[inline(always)]
unsafe fn strnlen_k<L: Lanes>(s: *const u8, max: usize) -> usize {
    // SAFETY: forwarded.
    unsafe { scan_k::<L>(s, None, max) }
}

/// [`scan_k`] for `strchrnul`.
///
/// # Safety
/// `s` must point to a NUL-terminated string.
#[inline(always)]
unsafe fn strchrnul_k<L: Lanes>(s: *const u8, c: u8) -> usize {
    // SAFETY: forwarded.
    unsafe { scan_k::<L>(s, Some(c), usize::MAX) }
}

dispatch_fn! {
    /// `strlen`.
    ///
    /// # Safety
    /// `s` must point to a NUL-terminated string.
    pub unsafe fn strlen(s: *const u8) -> usize = strlen_k;
}

dispatch_fn! {
    /// `strnlen`: like [`strlen`] but never looks past `max` bytes.
    ///
    /// # Safety
    /// `s` must be readable up to the NUL terminator or `max` bytes,
    /// whichever comes first.
    pub unsafe fn strnlen(s: *const u8, max: usize) -> usize = strnlen_k;
}

dispatch_fn! {
    /// `strchrnul`: offset of the first `c` or of the terminating NUL.
    ///
    /// # Safety
    /// `s` must point to a NUL-terminated string.
    pub unsafe fn strchrnul(s: *const u8, c: u8) -> usize = strchrnul_k;
}

/// `strchr` proper, for the C entry point.
///
/// # Safety
/// `s` must point to a NUL-terminated string.
#[inline(always)]
unsafe fn strchr_ptr_k<L: Lanes>(s: *const u8, c: u8) -> *mut u8 {
    // SAFETY: forwarded.
    let i = unsafe { scan_k::<L>(s, Some(c), usize::MAX) };
    // SAFETY: `i` is inside the string (at most the terminator).
    unsafe {
        if *s.add(i) == c {
            s.add(i) as *mut u8
        } else {
            core::ptr::null_mut()
        }
    }
}

dispatch_fn! {
    /// `strchr(3)` proper: a pointer to the first `c`, or null.
    ///
    /// # Safety
    /// `s` must point to a NUL-terminated string.
    pub unsafe fn strchr_ptr(s: *const u8, c: u8) -> *mut u8 = strchr_ptr_k;
}

// ---------------------------------------------------------------------
// memcmp / strcmp / strncmp

/// Byte difference at the first position where `a` and `b` differ.
#[inline(always)]
fn diff_at(a: &[u8], b: &[u8], k: usize) -> c_int {
    a[k] as c_int - b[k] as c_int
}

/// Scalar comparison of fewer than a vector's worth of bytes.
#[inline(always)]
fn memcmp_scalar(a: &[u8], b: &[u8], len: usize) -> c_int {
    let mut i = 0;
    while i + 8 <= len {
        let x = u64::from_ne_bytes(a[i..i + 8].try_into().unwrap());
        let y = u64::from_ne_bytes(b[i..i + 8].try_into().unwrap());
        if x != y {
            return diff_at(a, b, i + ((x ^ y).trailing_zeros() / 8) as usize);
        }
        i += 8;
    }
    while i < len {
        if a[i] != b[i] {
            return diff_at(a, b, i);
        }
        i += 1;
    }
    0
}

#[inline(always)]
fn memcmp_k<L: Lanes>(a: &[u8], b: &[u8]) -> c_int {
    let n = L::N;
    let len = a.len().min(b.len());
    let (pa, pb) = (a.as_ptr(), b.as_ptr());
    if len < n {
        if len == 0 {
            return 0;
        }
        if both_page_safe(pa, pb, n) {
            // SAFETY: unaligned over-reads inside the current pages.
            let (va, vb) = unsafe { (load::<L>(pa), load::<L>(pb)) };
            let m = va.eq(vb).not().bits() & low_bits(len);
            return if m == 0 {
                0
            } else {
                diff_at(a, b, m.trailing_zeros() as usize)
            };
        }
        return memcmp_scalar(a, b, len);
    }
    let mut i = 0;
    while i + 4 * n <= len {
        // SAFETY: all vectors are inside both slices.
        let (ea, eb, ec, ed) = unsafe {
            (
                load::<L>(pa.add(i)).eq(load::<L>(pb.add(i))),
                load::<L>(pa.add(i + n)).eq(load::<L>(pb.add(i + n))),
                load::<L>(pa.add(i + 2 * n)).eq(load::<L>(pb.add(i + 2 * n))),
                load::<L>(pa.add(i + 3 * n)).eq(load::<L>(pb.add(i + 3 * n))),
            )
        };
        if !ea.and(eb).and(ec).and(ed).all() {
            let (x, y, z, w) = (
                ea.not().bits(),
                eb.not().bits(),
                ec.not().bits(),
                ed.not().bits(),
            );
            let k = if x != 0 {
                x.trailing_zeros() as usize
            } else if y != 0 {
                n + y.trailing_zeros() as usize
            } else if z != 0 {
                2 * n + z.trailing_zeros() as usize
            } else {
                3 * n + w.trailing_zeros() as usize
            };
            return diff_at(a, b, i + k);
        }
        i += 4 * n;
    }
    while i + n <= len {
        // SAFETY: inside both slices.
        let m = unsafe { load::<L>(pa.add(i)).eq(load::<L>(pb.add(i))) }
            .not()
            .bits();
        if m != 0 {
            return diff_at(a, b, i + m.trailing_zeros() as usize);
        }
        i += n;
    }
    if i < len {
        let start = len - n;
        // SAFETY: inside both slices.
        let m = unsafe { load::<L>(pa.add(start)).eq(load::<L>(pb.add(start))) }
            .not()
            .bits()
            & !low_bits(i - start);
        if m != 0 {
            return diff_at(a, b, start + m.trailing_zeros() as usize);
        }
    }
    0
}

dispatch_fn! {
    /// `memcmp` over two equally long slices.
    pub fn memcmp(a: &[u8], b: &[u8]) -> c_int = memcmp_k;
}

/// Compares two NUL-terminated strings, looking at most at `limit` bytes.
///
/// # Safety
/// Both must be NUL-terminated (within `limit` bytes if `limit` is finite).
#[inline(always)]
unsafe fn strncmp_k<L: Lanes>(a: *const u8, b: *const u8, limit: usize) -> c_int {
    let n = L::N;
    let zero = L::splat(0);
    let mut i = 0;
    while i < limit {
        // SAFETY: both strings are readable up to their NUL terminators and
        // no NUL has been seen before `i`.
        let (pa, pb) = unsafe { (a.add(i), b.add(i)) };
        // Most strings end within the first vector, so look at that one
        // alone before switching to four at a time. `keep_eq` is zero
        // exactly where the comparison stops.
        if i >= n && i + 4 * n <= limit && both_page_safe(pa, pb, 4 * n) {
            // SAFETY: the loads stay within the current page of each string,
            // and both strings extend to at least `pa`/`pb`.
            let (t0, t1, t2, t3) = unsafe {
                (
                    load::<L>(pa).keep_eq(load::<L>(pb)),
                    load::<L>(pa.add(n)).keep_eq(load::<L>(pb.add(n))),
                    load::<L>(pa.add(2 * n)).keep_eq(load::<L>(pb.add(2 * n))),
                    load::<L>(pa.add(3 * n)).keep_eq(load::<L>(pb.add(3 * n))),
                )
            };
            if t0.min(t1).min(t2.min(t3)).eq(zero).any() {
                let (x, y, z, w) = (
                    t0.eq(zero).bits(),
                    t1.eq(zero).bits(),
                    t2.eq(zero).bits(),
                    t3.eq(zero).bits(),
                );
                let k = if x != 0 {
                    x.trailing_zeros() as usize
                } else if y != 0 {
                    n + y.trailing_zeros() as usize
                } else if z != 0 {
                    2 * n + z.trailing_zeros() as usize
                } else {
                    3 * n + w.trailing_zeros() as usize
                };
                // SAFETY: `k` is within the loaded vectors.
                return unsafe { *pa.add(k) as c_int - *pb.add(k) as c_int };
            }
            i += 4 * n;
        } else if i + n <= limit && both_page_safe(pa, pb, n) {
            // SAFETY: as above.
            let m = unsafe { load::<L>(pa).keep_eq(load::<L>(pb)) }
                .eq(zero)
                .bits();
            if m != 0 {
                let k = m.trailing_zeros() as usize;
                // SAFETY: `k` is within the loaded vectors.
                return unsafe { *pa.add(k) as c_int - *pb.add(k) as c_int };
            }
            i += n;
        } else if i + 8 <= limit && both_page_safe(pa, pb, 8) {
            // Near a page end: eight bytes at a time. The lowest set bit
            // of `zero` marks the first NUL of `x` exactly (higher bits may
            // be spurious), and the lowest set bit of `diff` the first
            // differing byte, so the lower of the two is the answer.
            // SAFETY: both reads stay inside the current page and start
            // inside the strings.
            let (x, y) = unsafe {
                (
                    pa.cast::<u64>().read_unaligned(),
                    pb.cast::<u64>().read_unaligned(),
                )
            };
            let zero = x.wrapping_sub(0x0101_0101_0101_0101) & !x & 0x8080_8080_8080_8080;
            let diff = x ^ y;
            if zero | diff != 0 {
                let k = ((zero | diff).trailing_zeros() / 8) as usize;
                // SAFETY: byte `k` is inside both strings.
                return unsafe { *pa.add(k) as c_int - *pb.add(k) as c_int };
            }
            i += 8;
        } else {
            // SAFETY: byte `i` is inside both strings.
            let (x, y) = unsafe { (*pa, *pb) };
            if x != y || x == 0 {
                return x as c_int - y as c_int;
            }
            i += 1;
        }
    }
    0
}

/// [`strncmp_k`] without a limit.
///
/// # Safety
/// Both strings must be NUL-terminated.
#[inline(always)]
unsafe fn strcmp_k<L: Lanes>(a: *const u8, b: *const u8) -> c_int {
    // SAFETY: forwarded.
    unsafe { strncmp_k::<L>(a, b, usize::MAX) }
}

dispatch_fn! {
    /// `strcmp`.
    ///
    /// # Safety
    /// Both strings must be NUL-terminated.
    pub unsafe fn strcmp(a: *const u8, b: *const u8) -> c_int = strcmp_k;
}

dispatch_fn! {
    /// `strncmp`.
    ///
    /// # Safety
    /// Both strings must be NUL-terminated or readable for `limit` bytes.
    pub unsafe fn strncmp(a: *const u8, b: *const u8, limit: usize) -> c_int = strncmp_k;
}

// ---------------------------------------------------------------------
// memmem

/// Result of the vectorised candidate scan.
enum Scan {
    Found(usize),
    NotFound,
    /// The verification budget ran out; no match starts before this offset.
    Budget(usize),
}

/// Scans for windows whose first and last bytes match the needle's and
/// verifies each candidate. Verification work is capped at a multiple
/// of the haystack length so that a needle like `aaaaaaaa` in a haystack
/// of `a`s cannot make this quadratic; when the cap is hit the caller
/// falls back to Two-Way.
#[inline(always)]
fn find_k<L: Lanes>(hay: &[u8], needle: &[u8]) -> Scan {
    let n = L::N;
    let (h, l) = (hay.len(), needle.len());
    let p = hay.as_ptr();
    let first = L::splat(needle[0]);
    let last = L::splat(needle[l - 1]);
    let inner = &needle[1..l - 1];
    let mut budget = 2 * h + 64;
    let mut i = 0;
    // Both the "first byte" vector at `i` and the "last byte" vector at
    // `i + l - 1` must be inside the haystack.
    while i + (l - 1) + n <= h {
        // SAFETY: both vectors are inside `hay`.
        let (a, b) = unsafe { (load::<L>(p.add(i)), load::<L>(p.add(i + l - 1))) };
        let mut m = a.eq(first).and(b.eq(last)).bits();
        while m != 0 {
            let k = i + m.trailing_zeros() as usize;
            if hay[k + 1..k + l - 1] == *inner {
                return Scan::Found(k);
            }
            budget = budget.saturating_sub(l);
            if budget == 0 {
                return Scan::Budget(k + 1);
            }
            m &= m - 1;
        }
        i += n;
    }
    // Fewer than a vector's worth of candidate windows remain.
    while i + l <= h {
        if hay[i] == needle[0] && hay[i + l - 1] == needle[l - 1] && hay[i + 1..i + l - 1] == *inner
        {
            return Scan::Found(i);
        }
        i += 1;
    }
    Scan::NotFound
}

dispatch_fn! {
    /// [`find_k`] for the detected level.
    fn find(hay: &[u8], needle: &[u8]) -> Scan = find_k;
}

/// Finds `needle` in `hay`.
///
/// A vectorised scan handles the common case; the Two-Way algorithm
/// ([`two_way`]) takes over when a pathological needle makes the scan's
/// verification work exceed its budget, so the total stays linear.
pub fn memmem(hay: &[u8], needle: &[u8]) -> Option<usize> {
    let l = needle.len();
    if l == 0 {
        return Some(0);
    }
    if l == 1 {
        return memchr(hay, needle[0]);
    }
    if hay.len() < l {
        return None;
    }
    match find(hay, needle) {
        Scan::Found(k) => Some(k),
        Scan::NotFound => None,
        Scan::Budget(from) => two_way(&hay[from..], needle).map(|k| k + from),
    }
}

/// Finds `needle` (at least two bytes, no longer than `hay`) in `hay`
/// using the Two-Way algorithm (Crochemore & Perrin), which runs in
/// `O(hay + needle)` time and constant space, so adversarial inputs
/// cannot make it quadratic.
///
/// This follows musl's `twoway_memmem`. The needle's maximal suffix and
/// period are computed with both orderings; the haystack is then scanned
/// with a shift table on the last needle byte for fast skipping.
fn two_way(hay: &[u8], needle: &[u8]) -> Option<usize> {
    let l = needle.len();
    debug_assert!(l >= 2);
    if hay.len() < l {
        return None;
    }
    let n = needle;
    // Byte set and last-occurrence shift table.
    let mut byteset = [0u64; 4];
    let mut shift = [0usize; 256];
    for (i, &c) in n.iter().enumerate() {
        byteset[(c >> 6) as usize] |= 1 << (c & 63);
        shift[c as usize] = i + 1;
    }
    let in_set = |c: u8| byteset[(c >> 6) as usize] & (1 << (c & 63)) != 0;

    // Maximal suffix under `<` and under `>`; keep the later one.
    let maximal_suffix = |greater: bool| -> (usize, usize) {
        let (mut ip, mut jp, mut k, mut p) = (usize::MAX, 0usize, 1usize, 1usize);
        while jp + k < l {
            let (x, y) = (n[ip.wrapping_add(k)], n[jp + k]);
            if x == y {
                if k == p {
                    jp += p;
                    k = 1;
                } else {
                    k += 1;
                }
            } else if (x > y) == greater {
                jp += k;
                k = 1;
                p = jp.wrapping_sub(ip);
            } else {
                ip = jp;
                jp += 1;
                k = 1;
                p = 1;
            }
        }
        (ip, p)
    };
    let (ms0, p0) = maximal_suffix(true);
    let (ms1, p1) = maximal_suffix(false);
    let (ms, mut p) = if ms1.wrapping_add(1) > ms0.wrapping_add(1) {
        (ms1, p1)
    } else {
        (ms0, p0)
    };

    // Is the needle periodic with period `p`?
    let mem0 = if n[..ms.wrapping_add(1)] == n[p..p + ms.wrapping_add(1)] {
        l - p
    } else {
        p = ms.wrapping_add(1).max(l - ms.wrapping_add(1)) + 1;
        0
    };
    let mut mem = 0usize;

    let mut h = 0usize;
    loop {
        if hay.len() - h < l {
            return None;
        }
        // Check the last byte first and skip using the shift table.
        let last = hay[h + l - 1];
        if !in_set(last) {
            h += l;
            mem = 0;
            continue;
        }
        let k = l - shift[last as usize];
        if k != 0 {
            h += k.max(mem);
            mem = 0;
            continue;
        }
        // Compare the right half, then the left half.
        let mut k = ms.wrapping_add(1).max(mem);
        while k < l && n[k] == hay[h + k] {
            k += 1;
        }
        if k < l {
            h += k - ms.wrapping_add(1) + 1;
            mem = 0;
            continue;
        }
        let mut k = ms.wrapping_add(1);
        while k > mem && n[k - 1] == hay[h + k - 1] {
            k -= 1;
        }
        if k <= mem {
            return Some(h);
        }
        h += p;
        mem = mem0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A simple deterministic PRNG so tests need no dependencies.
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

    #[repr(align(64))]
    struct Aligned([u8; 512]);

    fn for_each_level(f: impl Fn()) {
        use core::sync::atomic::Ordering;
        let supported = crate::arch::cpu::detect() as u8;
        for level in 0u8..=supported {
            super::super::simd::LEVEL_FOR_TESTS.store(level, Ordering::Relaxed);
            f();
        }
        super::super::simd::LEVEL_FOR_TESTS.store(0xff, Ordering::Relaxed);
    }

    #[test]
    fn memchr_matches_naive() {
        for_each_level(|| {
            let mut rng = Rng(0x1234_5678);
            for _ in 0..3000 {
                let len = rng.below(200);
                let hay: Vec<u8> = (0..len).map(|_| rng.below(4) as u8).collect();
                let needle = rng.below(5) as u8;
                assert_eq!(memchr(&hay, needle), hay.iter().position(|&b| b == needle));
                assert_eq!(
                    memrchr(&hay, needle),
                    hay.iter().rposition(|&b| b == needle)
                );
            }
        });
    }

    #[test]
    fn strlen_strnlen_strchrnul_all_alignments() {
        for_each_level(|| {
            let mut buf = Aligned([b'x'; 512]);
            for off in 0..70 {
                for len in 0..150 {
                    buf.0.fill(b'x');
                    buf.0[off + len] = 0;
                    let p = buf.0[off..].as_ptr();
                    // SAFETY: NUL-terminated inside the buffer.
                    unsafe {
                        assert_eq!(strlen(p), len, "off={off} len={len}");
                        assert_eq!(strnlen(p, usize::MAX), len);
                        assert_eq!(strnlen(p, len + 1), len);
                        assert_eq!(strnlen(p, len), len);
                        assert_eq!(strnlen(p, len / 2), len / 2);
                        assert_eq!(strnlen(p, 0), 0);
                        assert_eq!(strchrnul(p, b'y'), len);
                        assert_eq!(strchrnul(p, 0), len);
                        if len > 3 {
                            buf.0[off + len - 2] = b'y';
                            assert_eq!(strchrnul(p, b'y'), len - 2);
                        }
                    }
                }
            }
        });
    }

    #[test]
    fn memcmp_matches_naive() {
        for_each_level(|| {
            let mut rng = Rng(99);
            for _ in 0..3000 {
                let len = rng.below(100);
                let a: Vec<u8> = (0..len).map(|_| rng.below(3) as u8 + 0x7f).collect();
                let mut b = a.clone();
                if len > 0 && rng.below(2) == 0 {
                    let k = rng.below(len);
                    b[k] = b[k].wrapping_add(rng.below(255) as u8 + 1);
                }
                let expected = match a.iter().zip(&b).find(|(x, y)| x != y) {
                    Some((&x, &y)) => x as c_int - y as c_int,
                    None => 0,
                };
                assert_eq!(memcmp(&a, &b), expected);
            }
        });
    }

    #[test]
    fn strcmp_strncmp_including_page_crossing() {
        for_each_level(|| {
            // Two buffers placed at the end of a page so vector loads would
            // fault if the page-safety check were wrong.
            let page = MIN_PAGE_SIZE;
            let mut region_a = vec![0u8; 3 * page];
            let mut region_b = vec![0u8; 3 * page];
            let base_a = (region_a.as_ptr() as usize + page - 1) & !(page - 1);
            let base_b = (region_b.as_ptr() as usize + page - 1) & !(page - 1);
            let off_a = base_a - region_a.as_ptr() as usize;
            let off_b = base_b - region_b.as_ptr() as usize;
            let mut rng = Rng(7);
            for _ in 0..2000 {
                let len = rng.below(120);
                let s: Vec<u8> = (0..len).map(|_| b'a' + rng.below(2) as u8).collect();
                let mut t = s.clone();
                if len > 0 && rng.below(3) == 0 {
                    let k = rng.below(len);
                    t[k] = if rng.below(2) == 0 { b'z' } else { 0 };
                }
                // Positions straddling the page boundary in various ways.
                let pa = off_a + page - rng.below(len + 40);
                let pb = off_b + page - rng.below(len + 40);
                region_a[pa..pa + len].copy_from_slice(&s);
                region_a[pa + len] = 0;
                region_b[pb..pb + len].copy_from_slice(&t);
                region_b[pb + len] = 0;
                let cs = core::ffi::CStr::from_bytes_until_nul(&region_a[pa..]).unwrap();
                let ct = core::ffi::CStr::from_bytes_until_nul(&region_b[pb..]).unwrap();
                let expected = match cs.to_bytes().cmp(ct.to_bytes()) {
                    core::cmp::Ordering::Less => -1,
                    core::cmp::Ordering::Equal => 0,
                    core::cmp::Ordering::Greater => 1,
                };
                // SAFETY: both NUL-terminated.
                let r = unsafe { strcmp(region_a[pa..].as_ptr(), region_b[pb..].as_ptr()) };
                assert_eq!(r.signum(), expected, "{cs:?} vs {ct:?}");
                for limit in [0, 1, 5, 16, 17, 31, 32, 33, len, len + 1, 1000] {
                    let ls = &cs.to_bytes()[..cs.to_bytes().len().min(limit)];
                    let lt = &ct.to_bytes()[..ct.to_bytes().len().min(limit)];
                    let expected = match ls.cmp(lt) {
                        core::cmp::Ordering::Less => -1,
                        core::cmp::Ordering::Equal => 0,
                        core::cmp::Ordering::Greater => 1,
                    };
                    // SAFETY: both NUL-terminated.
                    let r =
                        unsafe { strncmp(region_a[pa..].as_ptr(), region_b[pb..].as_ptr(), limit) };
                    assert_eq!(r.signum(), expected, "limit={limit} {cs:?} vs {ct:?}");
                }
            }
        });
    }

    #[test]
    fn strcmp_is_unsigned() {
        // SAFETY: literals are NUL-terminated.
        unsafe {
            assert!(strcmp(b"\x80\0".as_ptr(), b"\x01\0".as_ptr()) > 0);
            assert!(strcmp(b"a\0".as_ptr(), b"ab\0".as_ptr()) < 0);
            assert!(strcmp(b"ab\0".as_ptr(), b"a\0".as_ptr()) > 0);
            assert_eq!(strcmp(b"\0".as_ptr(), b"\0".as_ptr()), 0);
        }
    }

    #[test]
    fn memchr_memcmp_small_inputs_at_page_edges() {
        for_each_level(|| {
            let page = MIN_PAGE_SIZE;
            let mut region = vec![0u8; 3 * page];
            let base = (region.as_ptr() as usize + page - 1) & !(page - 1);
            let off = base - region.as_ptr() as usize;
            let mut rng = Rng(5);
            for _ in 0..4000 {
                let len = rng.below(70);
                // Start anywhere from 70 bytes before the boundary to just after it.
                let start = off + page - rng.below(len + 72);
                let data: Vec<u8> = (0..len).map(|_| b'a' + rng.below(3) as u8).collect();
                region[start..start + len].copy_from_slice(&data);
                // Bytes outside the slice contain the needle, to catch masking bugs.
                region[start.saturating_sub(64)..start].fill(b'c');
                region[start + len..start + len + 64].fill(b'c');
                let hay = &region[start..start + len];
                assert_eq!(memchr(hay, b'c'), data.iter().position(|&b| b == b'c'));
                assert_eq!(memrchr(hay, b'c'), data.iter().rposition(|&b| b == b'c'));
                let mut other = data.clone();
                if len > 0 && rng.below(2) == 0 {
                    let k = rng.below(len);
                    other[k] ^= 1;
                }
                let expected = match data.iter().zip(&other).find(|(x, y)| x != y) {
                    Some((&x, &y)) => x as c_int - y as c_int,
                    None => 0,
                };
                assert_eq!(memcmp(hay, &other), expected);
                assert_eq!(memcmp(&other, hay), -expected);
            }
        });
    }

    #[test]
    fn memmem_matches_naive() {
        fn naive(h: &[u8], n: &[u8]) -> Option<usize> {
            if n.is_empty() {
                return Some(0);
            }
            h.windows(n.len()).position(|w| w == n)
        }
        for_each_level(|| {
            let mut rng = Rng(42);
            for _ in 0..20000 {
                let alphabet = 1 + rng.below(3);
                let long = rng.below(4) == 0;
                let hl = rng.below(if long { 300 } else { 60 });
                let nl = rng.below(8);
                let h: Vec<u8> = (0..hl).map(|_| b'a' + rng.below(alphabet) as u8).collect();
                let n: Vec<u8> = (0..nl).map(|_| b'a' + rng.below(alphabet) as u8).collect();
                assert_eq!(memmem(&h, &n), naive(&h, &n), "h={h:?} n={n:?}");
                if nl >= 2 && hl >= nl {
                    assert_eq!(two_way(&h, &n), naive(&h, &n), "two_way h={h:?} n={n:?}");
                }
            }
        });
        // A needle whose first and last bytes match everywhere exhausts
        // the scan's verification budget and falls back to Two-Way.
        let hay: Vec<u8> = core::iter::repeat_n(b'a', 20000).collect();
        let mut needle: Vec<u8> = core::iter::repeat_n(b'a', 40).collect();
        needle[20] = b'b';
        assert_eq!(memmem(&hay, &needle), None);
        let mut hay2 = hay.clone();
        hay2[19000] = b'b';
        assert_eq!(memmem(&hay2, &needle), Some(19000 - 20));
        assert_eq!(two_way(&hay2, &needle), Some(19000 - 20));
        // Periodic and pathological needles.
        let cases: &[(&[u8], &[u8])] = &[
            (b"aaaaaaaaaaaaaaaaaaaaaaaaab", b"aaaaab"),
            (b"abababababababababababc", b"ababababc"),
            (b"abcabcabcabcabd", b"abcabd"),
            (
                b"xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxy",
                b"xxxxxy",
            ),
            (b"hello world", b"o w"),
            (b"hello world", b"world"),
            (b"hello world", b"worlds"),
            (b"", b""),
            (b"", b"a"),
            (b"a", b""),
            (b"aaa", b"aaaa"),
            (b"mississippi", b"issip"),
            (b"mississippi", b"ssippi"),
            (b"GCATCGCAGAGAGTATACAGTACG", b"GCAGAGAG"),
        ];
        for (h, n) in cases {
            assert_eq!(memmem(h, n), naive(h, n), "h={h:?} n={n:?}");
        }
    }
}
