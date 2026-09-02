//! `memcpy`, `memmove`, `memset`, `memcmp` and relatives.
//!
//! Strategy (x86_64):
//!
//! * up to 64 bytes: branch on size and use a couple of overlapping
//!   unaligned SSE2 loads/stores, no loops, no dispatch;
//! * 65 to 256 bytes: two, four or eight vectors (16 or 32 bytes wide,
//!   see [`lanes`](crate::string::lanes); 64-byte stores are avoided
//!   because they cannot forward to the narrower loads that typically
//!   follow a copy), all loaded before any is stored, so the same code
//!   serves overlapping `memmove`; only SSE2 needs a loop for the upper
//!   part of this range;
//! * large copies/fills: `rep movsb` / `rep stosb`, which on every CPU with
//!   ERMS (2013+) is the fastest option and does not pollute the cache
//!   with vector stores. Overlapping `memmove`s of nearby buffers, where
//!   `rep movsb` is slow, use four-vector iterations instead.

use crate::string::lanes::Lanes;
use crate::string::search;
use crate::string::simd::dispatch_fn_ymm;
use core::arch::asm;
use core::arch::x86_64::{__m128i, _mm_loadu_si128, _mm_set1_epi8, _mm_storeu_si128};
use core::ffi::{c_int, c_void};
use core::{ptr, slice};

/// Sizes above this go to `rep movsb`/`rep stosb`.
const REP_THRESHOLD: usize = 256;

#[inline(always)]
unsafe fn load16(p: *const u8) -> __m128i {
    // SAFETY: caller guarantees 16 readable bytes.
    unsafe { _mm_loadu_si128(p as *const __m128i) }
}

#[inline(always)]
unsafe fn store16(p: *mut u8, v: __m128i) {
    // SAFETY: caller guarantees 16 writable bytes.
    unsafe { _mm_storeu_si128(p as *mut __m128i, v) }
}

/// Copies `n <= 64` bytes. Loads everything before storing, so `src` and
/// `dst` may overlap arbitrarily.
///
/// # Safety
/// Both pointers must be valid for `n` bytes.
#[inline(always)]
unsafe fn copy_small(dst: *mut u8, src: *const u8, n: usize) {
    // SAFETY: every access below stays inside `[0, n)` of both buffers.
    unsafe {
        if n >= 32 {
            let a = load16(src);
            let b = load16(src.add(16));
            let c = load16(src.add(n - 32));
            let d = load16(src.add(n - 16));
            store16(dst, a);
            store16(dst.add(16), b);
            store16(dst.add(n - 32), c);
            store16(dst.add(n - 16), d);
        } else if n >= 16 {
            let a = load16(src);
            let b = load16(src.add(n - 16));
            store16(dst, a);
            store16(dst.add(n - 16), b);
        } else if n >= 8 {
            let a = ptr::read_unaligned(src as *const u64);
            let b = ptr::read_unaligned(src.add(n - 8) as *const u64);
            ptr::write_unaligned(dst as *mut u64, a);
            ptr::write_unaligned(dst.add(n - 8) as *mut u64, b);
        } else if n >= 4 {
            let a = ptr::read_unaligned(src as *const u32);
            let b = ptr::read_unaligned(src.add(n - 4) as *const u32);
            ptr::write_unaligned(dst as *mut u32, a);
            ptr::write_unaligned(dst.add(n - 4) as *mut u32, b);
        } else if n >= 2 {
            let a = ptr::read_unaligned(src as *const u16);
            let b = ptr::read_unaligned(src.add(n - 2) as *const u16);
            ptr::write_unaligned(dst as *mut u16, a);
            ptr::write_unaligned(dst.add(n - 2) as *mut u16, b);
        } else if n == 1 {
            *dst = *src;
        }
    }
}

/// Copies `L::N < n <= 8 * L::N` bytes with two, four or eight vectors.
/// Loads everything before storing, so the buffers may overlap.
///
/// # Safety
/// Both pointers must be valid for `n` bytes.
#[inline(always)]
unsafe fn copy_vec<L: Lanes>(dst: *mut u8, src: *const u8, n: usize) {
    let v = L::N;
    // SAFETY: every access below stays inside `[0, n)` of both buffers.
    unsafe {
        if n <= 2 * v {
            let a = L::load(src);
            let b = L::load(src.add(n - v));
            a.store(dst);
            b.store(dst.add(n - v));
        } else if n <= 4 * v {
            let a = L::load(src);
            let b = L::load(src.add(v));
            let c = L::load(src.add(n - 2 * v));
            let d = L::load(src.add(n - v));
            a.store(dst);
            b.store(dst.add(v));
            c.store(dst.add(n - 2 * v));
            d.store(dst.add(n - v));
        } else {
            let a = L::load(src);
            let b = L::load(src.add(v));
            let c = L::load(src.add(2 * v));
            let d = L::load(src.add(3 * v));
            let e = L::load(src.add(n - 4 * v));
            let f = L::load(src.add(n - 3 * v));
            let g = L::load(src.add(n - 2 * v));
            let h = L::load(src.add(n - v));
            a.store(dst);
            b.store(dst.add(v));
            c.store(dst.add(2 * v));
            d.store(dst.add(3 * v));
            e.store(dst.add(n - 4 * v));
            f.store(dst.add(n - 3 * v));
            g.store(dst.add(n - 2 * v));
            h.store(dst.add(n - v));
        }
    }
}

/// Copies the remainder of a loop: `n <= 4 * L::N` bytes.
///
/// # Safety
/// Both pointers must be valid for `n` bytes.
#[inline(always)]
unsafe fn copy_rem<L: Lanes>(dst: *mut u8, src: *const u8, n: usize) {
    // SAFETY: forwarded; `copy_small` covers up to 64 bytes and `L::N`
    // is at most 64.
    unsafe {
        if n > L::N {
            copy_vec::<L>(dst, src, n);
        } else if n > 0 {
            copy_small(dst, src, n);
        }
    }
}

/// Forward copy of `n > L::N` bytes, four vectors per iteration; correct
/// when `dst` is below `src` or the buffers do not overlap.
///
/// The loop's stores are aligned to the vector size (so none straddles a
/// cache line): the first vector is loaded up front and stored last,
/// and the loop starts at the next aligned destination address.
///
/// # Safety
/// Both pointers must be valid for `n` bytes; if they overlap, `dst` must
/// be below `src`.
#[inline(always)]
unsafe fn copy_forward<L: Lanes>(dst: *mut u8, src: *const u8, n: usize) {
    let v = L::N;
    // SAFETY: bounds are maintained by the loop condition; the remainder
    // is copied from where the loop stopped, which the loop's stores cannot
    // have touched (they all lie below `dst + i <= src + i`). The head is
    // loaded before any store and stored after every other load.
    unsafe {
        let head = L::load(src);
        let mut i = (dst as usize).wrapping_neg() & (v - 1);
        while i + 4 * v <= n {
            let a = L::load(src.add(i));
            let b = L::load(src.add(i + v));
            let c = L::load(src.add(i + 2 * v));
            let d = L::load(src.add(i + 3 * v));
            a.store(dst.add(i));
            b.store(dst.add(i + v));
            c.store(dst.add(i + 2 * v));
            d.store(dst.add(i + 3 * v));
            i += 4 * v;
        }
        copy_rem::<L>(dst.add(i), src.add(i), n - i);
        head.store(dst);
    }
}

/// Backward copy of `n > L::N` bytes for overlapping buffers with
/// `dst > src`, with the loop's stores aligned as in [`copy_forward`]
/// (here the last vector is loaded first and stored last).
///
/// # Safety
/// Both pointers must be valid for `n` bytes.
#[inline(always)]
unsafe fn copy_backward<L: Lanes>(dst: *mut u8, src: *const u8, n: usize) {
    let v = L::N;
    // SAFETY: bounds are maintained by the loop condition; the head block
    // is copied last, and the loop's stores all lie above `src + end`.
    // The tail is loaded before any store and stored after every load.
    unsafe {
        let tail = L::load(src.add(n - v));
        let mut end = n - ((dst as usize + n) & (v - 1));
        while end >= 4 * v {
            end -= 4 * v;
            let a = L::load(src.add(end));
            let b = L::load(src.add(end + v));
            let c = L::load(src.add(end + 2 * v));
            let d = L::load(src.add(end + 3 * v));
            a.store(dst.add(end));
            b.store(dst.add(end + v));
            c.store(dst.add(end + 2 * v));
            d.store(dst.add(end + 3 * v));
        }
        copy_rem::<L>(dst, src, end);
        tail.store(dst.add(n - v));
    }
}

/// Copies `64 < n <= 256` bytes.
///
/// # Safety
/// Both pointers must be valid for `n` bytes; if they overlap, `dst` must
/// be below `src` unless `n <= 8 * L::N`.
#[inline(always)]
unsafe fn copy_mid<L: Lanes>(dst: *mut u8, src: *const u8, n: usize) {
    // SAFETY: forwarded.
    unsafe {
        if n <= 8 * L::N {
            copy_vec::<L>(dst, src, n);
        } else {
            copy_forward::<L>(dst, src, n);
        }
    }
}

/// Copies `64 < n <= 256` possibly overlapping bytes.
///
/// # Safety
/// Both pointers must be valid for `n` bytes.
#[inline(always)]
unsafe fn move_mid<L: Lanes>(dst: *mut u8, src: *const u8, n: usize) {
    // SAFETY: forwarded; direction chosen by overlap.
    unsafe {
        if n <= 8 * L::N {
            copy_vec::<L>(dst, src, n);
        } else if forward_ok(dst, src, n) {
            copy_forward::<L>(dst, src, n);
        } else {
            copy_backward::<L>(dst, src, n);
        }
    }
}

dispatch_fn_ymm! {
    /// [`copy_mid`] for the detected level.
    ///
    /// # Safety
    /// As for [`copy_mid`].
    unsafe fn copy_mid_any(dst: *mut u8, src: *const u8, n: usize) -> () = copy_mid;
}

dispatch_fn_ymm! {
    /// [`move_mid`] for the detected level.
    ///
    /// # Safety
    /// As for [`move_mid`].
    unsafe fn move_mid_any(dst: *mut u8, src: *const u8, n: usize) -> () = move_mid;
}

dispatch_fn_ymm! {
    /// [`copy_forward`] for the detected level.
    ///
    /// # Safety
    /// As for [`copy_forward`].
    unsafe fn copy_forward_any(dst: *mut u8, src: *const u8, n: usize) -> () = copy_forward;
}

dispatch_fn_ymm! {
    /// [`copy_backward`] for the detected level.
    ///
    /// # Safety
    /// As for [`copy_backward`].
    unsafe fn copy_backward_any(dst: *mut u8, src: *const u8, n: usize) -> () = copy_backward;
}

dispatch_fn_ymm! {
    /// [`set_mid`] for the detected level.
    ///
    /// # Safety
    /// As for [`set_mid`].
    unsafe fn set_mid_any(dst: *mut u8, b: u8, n: usize) -> () = set_mid;
}

/// True if a forward copy is correct: `dst` is below `src`, or the buffers
/// do not overlap.
#[inline(always)]
fn forward_ok(dst: *mut u8, src: *const u8, n: usize) -> bool {
    (dst as usize).wrapping_sub(src as usize) >= n
}

/// True if a forward copy from `src` to `dst` may use `rep movsb`: it
/// handles overlapping buffers correctly as long as the copy direction is
/// forward, but is slow when the distance is smaller than a cache line.
#[inline(always)]
fn rep_ok(dst: *mut u8, src: *const u8) -> bool {
    (src as usize).wrapping_sub(dst as usize) >= 64
}

/// Forward copy with `rep movsb`.
///
/// # Safety
/// Both pointers must be valid for `n` bytes; if they overlap, `dst` must
/// be below `src`.
#[inline(always)]
unsafe fn rep_movsb(dst: *mut u8, src: *const u8, n: usize) {
    // SAFETY: caller contract.
    unsafe {
        asm!("rep movsb", inout("rcx") n => _, inout("rdi") dst => _, inout("rsi") src => _,
             options(nostack, preserves_flags));
    }
}

/// Fills `64 < n <= 256` bytes.
///
/// # Safety
/// `dst` must be valid for `n` bytes.
#[inline(always)]
unsafe fn set_mid<L: Lanes>(dst: *mut u8, b: u8, n: usize) {
    let v = L::N;
    let x = L::splat(b);
    // SAFETY: every store stays inside `[0, n)`.
    unsafe {
        if n <= 2 * v {
            x.store(dst);
            x.store(dst.add(n - v));
        } else if n <= 4 * v {
            x.store(dst);
            x.store(dst.add(v));
            x.store(dst.add(n - 2 * v));
            x.store(dst.add(n - v));
        } else if n <= 8 * v {
            x.store(dst);
            x.store(dst.add(v));
            x.store(dst.add(2 * v));
            x.store(dst.add(3 * v));
            x.store(dst.add(n - 4 * v));
            x.store(dst.add(n - 3 * v));
            x.store(dst.add(n - 2 * v));
            x.store(dst.add(n - v));
        } else {
            // Only reached with 16-byte vectors.
            let mut i = 0;
            while i + 4 * v <= n {
                x.store(dst.add(i));
                x.store(dst.add(i + v));
                x.store(dst.add(i + 2 * v));
                x.store(dst.add(i + 3 * v));
                i += 4 * v;
            }
            x.store(dst.add(n - 4 * v));
            x.store(dst.add(n - 3 * v));
            x.store(dst.add(n - 2 * v));
            x.store(dst.add(n - v));
        }
    }
}

/// `memcpy(3)`.
///
/// # Safety
/// `dst` and `src` must be valid for `n` bytes and must not overlap.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn memcpy(dst: *mut c_void, src: *const c_void, n: usize) -> *mut c_void {
    let (d, s) = (dst as *mut u8, src as *const u8);
    // SAFETY: forwarded from the caller.
    unsafe {
        if n <= 64 {
            copy_small(d, s, n);
        } else if n <= REP_THRESHOLD {
            copy_mid_any(d, s, n);
        } else if rep_ok(d, s) {
            rep_movsb(d, s, n);
        } else {
            copy_forward_any(d, s, n);
        }
    }
    dst
}

/// `memmove(3)`.
///
/// # Safety
/// `dst` and `src` must be valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn memmove(dst: *mut c_void, src: *const c_void, n: usize) -> *mut c_void {
    let (d, s) = (dst as *mut u8, src as *const u8);
    // SAFETY: forwarded from the caller; direction chosen by overlap.
    unsafe {
        if n <= 64 {
            copy_small(d, s, n);
        } else if n <= REP_THRESHOLD {
            move_mid_any(d, s, n);
        } else if forward_ok(d, s, n) {
            if rep_ok(d, s) {
                rep_movsb(d, s, n);
            } else {
                copy_forward_any(d, s, n);
            }
        } else {
            copy_backward_any(d, s, n);
        }
    }
    dst
}

/// `memset(3)`.
///
/// # Safety
/// `dst` must be valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn memset(dst: *mut c_void, c: c_int, n: usize) -> *mut c_void {
    let d = dst as *mut u8;
    let b = c as u8;
    // SAFETY: every access stays inside `[0, n)`.
    unsafe {
        if n >= 16 {
            let v = _mm_set1_epi8(b as i8);
            if n <= 32 {
                store16(d, v);
                store16(d.add(n - 16), v);
            } else if n <= 64 {
                store16(d, v);
                store16(d.add(16), v);
                store16(d.add(n - 32), v);
                store16(d.add(n - 16), v);
            } else if n <= REP_THRESHOLD {
                set_mid_any(d, b, n);
            } else {
                asm!("rep stosb", inout("rcx") n => _, inout("rdi") d => _, in("al") b,
                     options(nostack, preserves_flags));
            }
        } else if n >= 8 {
            let w = u64::from_ne_bytes([b; 8]);
            ptr::write_unaligned(d as *mut u64, w);
            ptr::write_unaligned(d.add(n - 8) as *mut u64, w);
        } else if n >= 4 {
            let w = u32::from_ne_bytes([b; 4]);
            ptr::write_unaligned(d as *mut u32, w);
            ptr::write_unaligned(d.add(n - 4) as *mut u32, w);
        } else if n >= 2 {
            let w = u16::from_ne_bytes([b; 2]);
            ptr::write_unaligned(d as *mut u16, w);
            ptr::write_unaligned(d.add(n - 2) as *mut u16, w);
        } else if n == 1 {
            *d = b;
        }
    }
    dst
}

/// `memcmp(3)`.
///
/// # Safety
/// Both pointers must be valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn memcmp(a: *const c_void, b: *const c_void, n: usize) -> c_int {
    // SAFETY: forwarded from the caller.
    let (a, b) = unsafe {
        (
            slice::from_raw_parts(a as *const u8, n),
            slice::from_raw_parts(b as *const u8, n),
        )
    };
    search::memcmp(a, b)
}

/// `bcmp(3)`: like `memcmp` but only the zero/non-zero result matters.
///
/// # Safety
/// Both pointers must be valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn bcmp(a: *const c_void, b: *const c_void, n: usize) -> c_int {
    // SAFETY: forwarded from the caller.
    unsafe { memcmp(a, b, n) }
}

/// `memchr(3)`.
///
/// # Safety
/// `s` must be valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn memchr(s: *const c_void, c: c_int, n: usize) -> *mut c_void {
    // SAFETY: forwarded from the caller.
    unsafe { search::memchr_ptr(s as *const u8, c as u8, n) as *mut c_void }
}

/// `memrchr(3)`.
///
/// # Safety
/// `s` must be valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn memrchr(s: *const c_void, c: c_int, n: usize) -> *mut c_void {
    // SAFETY: forwarded from the caller.
    let hay = unsafe { slice::from_raw_parts(s as *const u8, n) };
    match search::memrchr(hay, c as u8) {
        // SAFETY: `i < n`.
        Some(i) => unsafe { (s as *mut u8).add(i) as *mut c_void },
        None => ptr::null_mut(),
    }
}

/// `memccpy(3)`: copies up to `n` bytes, stopping after the first `c`.
/// Returns a pointer past the copied `c`, or NULL if `c` was not found.
///
/// # Safety
/// `dst` and `src` must be valid for `n` bytes and must not overlap.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn memccpy(
    dst: *mut c_void,
    src: *const c_void,
    c: c_int,
    n: usize,
) -> *mut c_void {
    // SAFETY: forwarded from the caller.
    let hay = unsafe { slice::from_raw_parts(src as *const u8, n) };
    match search::memchr(hay, c as u8) {
        Some(i) => {
            // SAFETY: `i + 1 <= n`.
            unsafe {
                memcpy(dst, src, i + 1);
                (dst as *mut u8).add(i + 1) as *mut c_void
            }
        }
        None => {
            // SAFETY: forwarded.
            unsafe { memcpy(dst, src, n) };
            ptr::null_mut()
        }
    }
}

/// `memmem(3)`.
///
/// # Safety
/// `hay` must be valid for `hay_len` bytes and `needle` for `needle_len`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn memmem(
    hay: *const c_void,
    hay_len: usize,
    needle: *const c_void,
    needle_len: usize,
) -> *mut c_void {
    // SAFETY: forwarded from the caller.
    let (h, n) = unsafe {
        (
            slice::from_raw_parts(hay as *const u8, hay_len),
            slice::from_raw_parts(needle as *const u8, needle_len),
        )
    };
    match search::memmem(h, n) {
        Some(i) => h[i..].as_ptr() as *mut c_void,
        None => ptr::null_mut(),
    }
}

/// `bcopy(3)`: legacy `memmove` with swapped arguments.
///
/// # Safety
/// Both pointers must be valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn bcopy(src: *const c_void, dst: *mut c_void, n: usize) {
    // SAFETY: forwarded from the caller.
    unsafe {
        memmove(dst, src, n);
    }
}

/// `ffs(3)`: index (1-based) of the least significant set bit, or 0.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn ffs(i: c_int) -> c_int {
    if i == 0 {
        0
    } else {
        i.trailing_zeros() as c_int + 1
    }
}

/// `ffsl(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn ffsl(i: core::ffi::c_long) -> c_int {
    if i == 0 {
        0
    } else {
        i.trailing_zeros() as c_int + 1
    }
}

/// `ffsll(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn ffsll(i: core::ffi::c_longlong) -> c_int {
    if i == 0 {
        0
    } else {
        i.trailing_zeros() as c_int + 1
    }
}

/// `bzero(3)`.
///
/// # Safety
/// `dst` must be valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn bzero(dst: *mut c_void, n: usize) {
    // SAFETY: forwarded from the caller.
    unsafe {
        memset(dst, 0, n);
    }
}

/// `explicit_bzero(3)`: a `memset` to zero that the optimiser may not
/// remove even if the memory is never read again.
///
/// # Safety
/// `dst` must be valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn explicit_bzero(dst: *mut c_void, n: usize) {
    // SAFETY: forwarded from the caller.
    unsafe {
        memset(dst, 0, n);
        // An empty asm block that claims to read the buffer keeps the
        // stores alive.
        asm!("/* {0} */", in(reg) dst, options(nostack, preserves_flags, readonly));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pattern(n: usize, seed: u8) -> Vec<u8> {
        (0..n)
            .map(|i| (i as u8).wrapping_mul(31).wrapping_add(seed))
            .collect()
    }

    #[test]
    fn memcpy_all_small_sizes_and_alignments() {
        for n in 0..300 {
            for off in 0..8 {
                let src = pattern(n + 16, 7);
                let mut dst = vec![0u8; n + 32];
                // SAFETY: buffers are large enough.
                unsafe { memcpy(dst.as_mut_ptr().add(off) as _, src.as_ptr().add(3) as _, n) };
                assert_eq!(&dst[off..off + n], &src[3..3 + n], "n={n} off={off}");
                assert!(dst[..off].iter().all(|&b| b == 0));
                assert!(dst[off + n..].iter().all(|&b| b == 0));
            }
        }
    }

    #[test]
    fn memcpy_large() {
        let src = pattern(100_000, 1);
        let mut dst = vec![0u8; 100_001];
        // SAFETY: buffers are large enough.
        unsafe { memcpy(dst.as_mut_ptr().add(1) as _, src.as_ptr() as _, 100_000) };
        assert_eq!(&dst[1..], &src[..]);
    }

    #[test]
    fn memmove_overlapping_both_directions() {
        for n in (0..600).chain([1000, 4096, 10_000]) {
            for shift in (1..40).chain([63, 64, 65, 100, 300]) {
                let orig = pattern(n + 300, 3);
                // Forward overlap: dst > src.
                let mut buf = orig.clone();
                // SAFETY: within the buffer.
                unsafe { memmove(buf.as_mut_ptr().add(shift) as _, buf.as_ptr() as _, n) };
                assert_eq!(
                    &buf[shift..shift + n],
                    &orig[..n],
                    "fwd n={n} shift={shift}"
                );
                // Backward overlap: dst < src.
                let mut buf = orig.clone();
                // SAFETY: within the buffer.
                unsafe { memmove(buf.as_mut_ptr() as _, buf.as_ptr().add(shift) as _, n) };
                assert_eq!(
                    &buf[..n],
                    &orig[shift..shift + n],
                    "bwd n={n} shift={shift}"
                );
            }
        }
    }

    #[test]
    fn memset_all_sizes() {
        for n in 0..600 {
            let mut buf = vec![0xEEu8; n + 16];
            // SAFETY: within the buffer.
            unsafe { memset(buf.as_mut_ptr().add(5) as _, 0x1A5, n) };
            assert!(buf[..5].iter().all(|&b| b == 0xEE));
            assert!(buf[5..5 + n].iter().all(|&b| b == 0xA5), "n={n}");
            assert!(buf[5 + n..].iter().all(|&b| b == 0xEE));
        }
    }

    #[test]
    fn memcmp_finds_first_difference() {
        for n in 0..100 {
            for k in 0..n {
                let a = pattern(n, 9);
                let mut b = a.clone();
                b[k] = b[k].wrapping_add(1);
                // SAFETY: equal lengths.
                let r = unsafe { memcmp(a.as_ptr() as _, b.as_ptr() as _, n) };
                let expected = a[k] as i32 - b[k] as i32;
                assert_eq!(r, expected, "n={n} k={k}");
                // SAFETY: as above.
                assert_eq!(
                    unsafe { memcmp(b.as_ptr() as _, a.as_ptr() as _, n) },
                    -expected
                );
            }
            let a = pattern(n, 9);
            // SAFETY: as above.
            assert_eq!(
                unsafe { memcmp(a.as_ptr() as _, a.clone().as_ptr() as _, n) },
                0
            );
        }
    }

    #[test]
    fn memchr_memrchr_memccpy() {
        let hay = b"hello world";
        // SAFETY: in bounds.
        unsafe {
            let p = memchr(hay.as_ptr() as _, b'o' as c_int, hay.len());
            assert_eq!(p as *const u8, hay.as_ptr().add(4));
            let p = memrchr(hay.as_ptr() as _, b'o' as c_int, hay.len());
            assert_eq!(p as *const u8, hay.as_ptr().add(7));
            assert!(memchr(hay.as_ptr() as _, b'z' as c_int, hay.len()).is_null());
            // The int argument is converted to unsigned char.
            let p = memchr(hay.as_ptr() as _, b'o' as c_int + 256, hay.len());
            assert_eq!(p as *const u8, hay.as_ptr().add(4));
            let mut dst = [0u8; 11];
            let p = memccpy(dst.as_mut_ptr() as _, hay.as_ptr() as _, b' ' as c_int, 11);
            assert_eq!(p as *const u8, dst.as_ptr().add(6));
            assert_eq!(&dst[..6], b"hello ");
            assert_eq!(dst[6], 0);
            assert!(memccpy(dst.as_mut_ptr() as _, hay.as_ptr() as _, b'z' as c_int, 11).is_null());
            assert_eq!(&dst, hay);
            let p = memmem(hay.as_ptr() as _, hay.len(), b"o w".as_ptr() as _, 3);
            assert_eq!(p as *const u8, hay.as_ptr().add(4));
        }
    }

    #[test]
    fn memcmp_is_unsigned() {
        // SAFETY: valid one byte buffers.
        assert!(unsafe { memcmp([0x80u8].as_ptr() as _, [0x01u8].as_ptr() as _, 1) } > 0);
    }
}
