//! SIMD kernels for searching and comparing bytes.
//!
//! Every kernel is generic over the SIMD level `S` and instantiated by
//! [`dispatch!`](crate::string::simd::dispatch). Two kinds of loads are
//! used:
//!
//! * slice loads for length-delimited data (`memchr`, `memcmp`), which
//!   are plainly in bounds;
//! * aligned "over-reads" for NUL-terminated strings (`strlen`,
//!   `strchr`), which read whole vectors from vector-aligned addresses. An
//!   aligned vector never crosses a page boundary, so if any byte of it is
//!   inside the string, the whole load is backed by readable memory.
//!   This is the standard technique used by every libc and by Rust's own
//!   `compiler_builtins`.
//!
//! For two-string kernels (`strcmp`) whose pointers have different
//! alignments the loads are unaligned instead, and only performed when
//! they provably stay inside the current page.

use crate::string::simd::dispatch;
use crate::sys::PAGE_SIZE;
use core::ffi::c_int;
use fearless_simd::prelude::*;

/// Native u8 vector of level `S`.
type V<S> = <S as Simd>::u8s;

/// Loads one vector from `p`.
///
/// # Safety
/// `p` must be valid for reads of `V::<S>::N` bytes in the sense
/// described in the module documentation.
#[inline(always)]
unsafe fn load<S: Simd>(simd: S, p: *const u8) -> V<S> {
    // SAFETY: caller guarantees readability.
    V::<S>::from_slice(simd, unsafe { core::slice::from_raw_parts(p, V::<S>::N) })
}

/// True if a read of `n` bytes at `p` stays inside one page.
#[inline(always)]
fn page_safe(p: *const u8, n: usize) -> bool {
    (p as usize & (PAGE_SIZE - 1)) <= PAGE_SIZE - n
}

/// Bit mask with one bit per lane of `V<S>`.
#[inline(always)]
fn lane_mask<S: Simd>() -> u64 {
    if V::<S>::N >= 64 {
        u64::MAX
    } else {
        (1u64 << V::<S>::N) - 1
    }
}

// ---------------------------------------------------------------------
// memchr / memrchr

#[inline(always)]
fn memchr_k<S: Simd>(simd: S, hay: &[u8], needle: u8) -> Option<usize> {
    let n = V::<S>::N;
    if hay.len() < n {
        return hay.iter().position(|&b| b == needle);
    }
    let v = V::<S>::splat(simd, needle);
    let mut i = 0;
    while i + n <= hay.len() {
        let m = V::<S>::from_slice(simd, &hay[i..i + n])
            .simd_eq(v)
            .to_bitmask();
        if m != 0 {
            return Some(i + m.trailing_zeros() as usize);
        }
        i += n;
    }
    if i < hay.len() {
        let start = hay.len() - n;
        let m = V::<S>::from_slice(simd, &hay[start..])
            .simd_eq(v)
            .to_bitmask();
        if m != 0 {
            return Some(start + m.trailing_zeros() as usize);
        }
    }
    None
}

/// Index of the first `needle` in `hay`.
#[inline]
pub fn memchr(hay: &[u8], needle: u8) -> Option<usize> {
    dispatch!(simd => memchr_k(simd, hay, needle))
}

#[inline(always)]
fn memrchr_k<S: Simd>(simd: S, hay: &[u8], needle: u8) -> Option<usize> {
    let n = V::<S>::N;
    if hay.len() < n {
        return hay.iter().rposition(|&b| b == needle);
    }
    let v = V::<S>::splat(simd, needle);
    let mut end = hay.len();
    while end >= n {
        let m = V::<S>::from_slice(simd, &hay[end - n..end])
            .simd_eq(v)
            .to_bitmask();
        if m != 0 {
            return Some(end - n + (63 - m.leading_zeros() as usize));
        }
        end -= n;
    }
    if end > 0 {
        let m = V::<S>::from_slice(simd, &hay[..n]).simd_eq(v).to_bitmask() & ((1u64 << end) - 1);
        if m != 0 {
            return Some(63 - m.leading_zeros() as usize);
        }
    }
    None
}

/// Index of the last `needle` in `hay`.
#[inline]
pub fn memrchr(hay: &[u8], needle: u8) -> Option<usize> {
    dispatch!(simd => memrchr_k(simd, hay, needle))
}

// ---------------------------------------------------------------------
// strlen / strnlen / strchrnul

/// Scans forward from `s` for the first byte that is NUL (or, if
/// `needle` is `Some`, NUL or the needle) and returns its offset.
///
/// # Safety
/// `s` must point to a NUL-terminated string.
#[inline(always)]
unsafe fn scan_k<S: Simd>(simd: S, s: *const u8, needle: Option<u8>, limit: usize) -> usize {
    let n = V::<S>::N;
    let start = s as usize;
    let mut p = start & !(n - 1);
    let zero = V::<S>::splat(simd, 0);
    let needle = V::<S>::splat(simd, needle.unwrap_or(0));
    // SAFETY: aligned over-read, see the module documentation.
    let v = unsafe { load(simd, p as *const u8) };
    // Ignore the bytes of the first vector that precede `start`.
    let m = (v.simd_eq(zero) | v.simd_eq(needle)).to_bitmask() >> (start - p);
    if m != 0 {
        return (m.trailing_zeros() as usize).min(limit);
    }
    loop {
        p += n;
        if p - start >= limit {
            return limit;
        }
        // SAFETY: as above; the previous vector contained no NUL, so the
        // string extends at least to `p`.
        let v = unsafe { load(simd, p as *const u8) };
        let m = (v.simd_eq(zero) | v.simd_eq(needle)).to_bitmask();
        if m != 0 {
            return (p - start + m.trailing_zeros() as usize).min(limit);
        }
    }
}

/// `strlen`.
///
/// # Safety
/// `s` must point to a NUL-terminated string.
#[inline]
pub unsafe fn strlen(s: *const u8) -> usize {
    // SAFETY: forwarded.
    dispatch!(simd => unsafe { scan_k(simd, s, None, usize::MAX) })
}

/// `strnlen`: like [`strlen`] but never looks past `max` bytes.
///
/// # Safety
/// `s` must be readable up to the NUL terminator or `max` bytes,
/// whichever comes first.
#[inline]
pub unsafe fn strnlen(s: *const u8, max: usize) -> usize {
    // SAFETY: forwarded.
    dispatch!(simd => unsafe { scan_k(simd, s, None, max) })
}

/// `strchrnul`: offset of the first `c` or of the terminating NUL.
///
/// # Safety
/// `s` must point to a NUL-terminated string.
#[inline]
pub unsafe fn strchrnul(s: *const u8, c: u8) -> usize {
    // SAFETY: forwarded.
    dispatch!(simd => unsafe { scan_k(simd, s, Some(c), usize::MAX) })
}

// ---------------------------------------------------------------------
// memcmp / strcmp / strncmp

/// Byte difference at the first position where `a` and `b` differ.
#[inline(always)]
fn diff_at(a: &[u8], b: &[u8], k: usize) -> c_int {
    a[k] as c_int - b[k] as c_int
}

#[inline(always)]
fn memcmp_k<S: Simd>(simd: S, a: &[u8], b: &[u8]) -> c_int {
    let n = V::<S>::N;
    let len = a.len().min(b.len());
    let mut i = 0;
    while i + n <= len {
        let m = !V::<S>::from_slice(simd, &a[i..i + n])
            .simd_eq(V::<S>::from_slice(simd, &b[i..i + n]))
            .to_bitmask()
            & lane_mask::<S>();
        if m != 0 {
            return diff_at(a, b, i + m.trailing_zeros() as usize);
        }
        i += n;
    }
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

/// `memcmp` over two equally long slices.
#[inline]
pub fn memcmp(a: &[u8], b: &[u8]) -> c_int {
    dispatch!(simd => memcmp_k(simd, a, b))
}

/// Compares two NUL-terminated strings, looking at most at `limit` bytes.
///
/// # Safety
/// Both must be NUL-terminated (within `limit` bytes if `limit` is finite).
#[inline(always)]
unsafe fn strncmp_k<S: Simd>(simd: S, a: *const u8, b: *const u8, limit: usize) -> c_int {
    let n = V::<S>::N;
    let zero = V::<S>::splat(simd, 0);
    let mut i = 0;
    while i < limit {
        // SAFETY: both strings are readable up to their NUL terminators and
        // no NUL has been seen before `i`.
        let (pa, pb) = unsafe { (a.add(i), b.add(i)) };
        if i + n <= limit && page_safe(pa, n) && page_safe(pb, n) {
            // SAFETY: the loads stay within the current page of each string,
            // and the string extends to at least `pa`.
            let (va, vb) = unsafe { (load(simd, pa), load(simd, pb)) };
            let m =
                (va.simd_eq(zero).to_bitmask() | !va.simd_eq(vb).to_bitmask()) & lane_mask::<S>();
            if m != 0 {
                let k = m.trailing_zeros() as usize;
                // SAFETY: `k` is within the loaded vectors.
                return unsafe { *pa.add(k) as c_int - *pb.add(k) as c_int };
            }
            i += n;
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

/// `strcmp`.
///
/// # Safety
/// Both strings must be NUL-terminated.
#[inline]
pub unsafe fn strcmp(a: *const u8, b: *const u8) -> c_int {
    // SAFETY: forwarded.
    dispatch!(simd => unsafe { strncmp_k(simd, a, b, usize::MAX) })
}

/// `strncmp`.
///
/// # Safety
/// Both strings must be NUL-terminated or readable for `limit` bytes.
#[inline]
pub unsafe fn strncmp(a: *const u8, b: *const u8, limit: usize) -> c_int {
    // SAFETY: forwarded.
    dispatch!(simd => unsafe { strncmp_k(simd, a, b, limit) })
}

// ---------------------------------------------------------------------
// memmem (Two-Way)

/// Finds `needle` in `hay` using the Two-Way algorithm (Crochemore &
/// Perrin), which runs in `O(hay + needle)` time and constant space, so
/// adversarial inputs cannot make it quadratic.
///
/// This follows musl's `twoway_memmem`. The needle's maximal suffix and
/// period are computed with both orderings; the haystack is then scanned
/// with a shift table on the last needle byte for fast skipping.
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
        for level in [0u8, 1] {
            if level == 1 && crate::arch::cpu::detect() != crate::arch::cpu::Level::Avx2 {
                continue;
            }
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
            let page = PAGE_SIZE;
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
    fn memmem_matches_naive() {
        fn naive(h: &[u8], n: &[u8]) -> Option<usize> {
            if n.is_empty() {
                return Some(0);
            }
            h.windows(n.len()).position(|w| w == n)
        }
        let mut rng = Rng(42);
        for _ in 0..20000 {
            let alphabet = 1 + rng.below(3);
            let hl = rng.below(60);
            let nl = rng.below(8);
            let h: Vec<u8> = (0..hl).map(|_| b'a' + rng.below(alphabet) as u8).collect();
            let n: Vec<u8> = (0..nl).map(|_| b'a' + rng.below(alphabet) as u8).collect();
            assert_eq!(memmem(&h, &n), naive(&h, &n), "h={h:?} n={n:?}");
        }
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
