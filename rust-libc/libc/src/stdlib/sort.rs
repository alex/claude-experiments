//! `qsort`, `qsort_r` and `bsearch`.
//!
//! `qsort` is an introsort-free, allocation-free **heapsort**: O(n log n)
//! worst case with no recursion, so untrusted comparison functions and
//! adversarial inputs cannot exhaust the stack or go quadratic. This is
//! the same choice musl made (it uses smoothsort), trading a little
//! constant-factor speed for robustness and simplicity.

use core::ffi::{c_int, c_void};
use core::ptr;

type Cmp = unsafe extern "C" fn(*const c_void, *const c_void) -> c_int;
type CmpR = unsafe extern "C" fn(*const c_void, *const c_void, *mut c_void) -> c_int;

/// Swaps two elements of `size` bytes.
///
/// # Safety
/// Both pointers must be valid for `size` bytes and not overlap.
#[inline]
unsafe fn swap(a: *mut u8, b: *mut u8, size: usize) {
    // SAFETY: caller contract.
    unsafe {
        let mut i = 0;
        while i + 8 <= size {
            let x = ptr::read_unaligned(a.add(i) as *const u64);
            let y = ptr::read_unaligned(b.add(i) as *const u64);
            ptr::write_unaligned(a.add(i) as *mut u64, y);
            ptr::write_unaligned(b.add(i) as *mut u64, x);
            i += 8;
        }
        while i < size {
            let x = *a.add(i);
            *a.add(i) = *b.add(i);
            *b.add(i) = x;
            i += 1;
        }
    }
}

/// Heapsort of `n` elements of `size` bytes at `base`, ordered by `cmp`.
///
/// # Safety
/// `base` must be valid for `n * size` bytes.
unsafe fn heapsort(
    base: *mut u8,
    n: usize,
    size: usize,
    mut cmp: impl FnMut(*const u8, *const u8) -> c_int,
) {
    if n < 2 {
        return;
    }
    // SAFETY: all indices are below `n`.
    let at = |i: usize| unsafe { base.add(i * size) };
    let mut sift_down = |mut root: usize, end: usize| {
        loop {
            let mut child = 2 * root + 1;
            if child >= end {
                break;
            }
            if child + 1 < end && cmp(at(child), at(child + 1)) < 0 {
                child += 1;
            }
            if cmp(at(root), at(child)) >= 0 {
                break;
            }
            // SAFETY: distinct elements inside the array.
            unsafe { swap(at(root), at(child), size) };
            root = child;
        }
    };
    for start in (0..n / 2).rev() {
        sift_down(start, n);
    }
    for end in (1..n).rev() {
        // SAFETY: distinct elements inside the array.
        unsafe { swap(at(0), at(end), size) };
        sift_down(0, end);
    }
}

/// `qsort(3)`.
///
/// # Safety
/// `base` must be valid for `n * size` bytes; `cmp` must be a valid
/// comparison function.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn qsort(base: *mut c_void, n: usize, size: usize, cmp: Cmp) {
    // SAFETY: forwarded.
    unsafe {
        heapsort(base as *mut u8, n, size, |a, b| {
            cmp(a as *const c_void, b as *const c_void)
        })
    }
}

/// `qsort_r(3)` (glibc argument order).
///
/// # Safety
/// As for [`qsort`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn qsort_r(
    base: *mut c_void,
    n: usize,
    size: usize,
    cmp: CmpR,
    arg: *mut c_void,
) {
    // SAFETY: forwarded.
    unsafe {
        heapsort(base as *mut u8, n, size, |a, b| {
            cmp(a as *const c_void, b as *const c_void, arg)
        })
    }
}

/// `bsearch(3)`.
///
/// # Safety
/// `base` must be valid for `n * size` bytes and sorted according to
/// `cmp`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn bsearch(
    key: *const c_void,
    base: *const c_void,
    n: usize,
    size: usize,
    cmp: Cmp,
) -> *mut c_void {
    let (mut lo, mut hi) = (0usize, n);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        // SAFETY: `mid < n`.
        let elem = unsafe { (base as *const u8).add(mid * size) as *const c_void };
        // SAFETY: caller contract.
        let r = unsafe { cmp(key, elem) };
        match r {
            0 => return elem as *mut c_void,
            r if r < 0 => hi = mid,
            _ => lo = mid + 1,
        }
    }
    ptr::null_mut()
}

#[cfg(test)]
mod tests {
    use super::*;

    unsafe extern "C" fn cmp_i32(a: *const c_void, b: *const c_void) -> c_int {
        // SAFETY: the test passes i32 pointers.
        unsafe { (*(a as *const i32)).cmp(&*(b as *const i32)) as c_int }
    }

    unsafe extern "C" fn cmp_rev(a: *const c_void, b: *const c_void, _: *mut c_void) -> c_int {
        // SAFETY: the test passes i32 pointers.
        unsafe { (*(b as *const i32)).cmp(&*(a as *const i32)) as c_int }
    }

    #[test]
    fn sorts_and_searches() {
        let mut seed = 12345u32;
        for n in [0usize, 1, 2, 3, 10, 100, 1000] {
            let mut v: Vec<i32> = (0..n)
                .map(|_| {
                    seed = seed.wrapping_mul(1103515245).wrapping_add(12345);
                    (seed >> 16) as i32 % 50
                })
                .collect();
            let mut expected = v.clone();
            expected.sort();
            // SAFETY: valid array and comparison.
            unsafe { qsort(v.as_mut_ptr() as _, n, 4, cmp_i32) };
            assert_eq!(v, expected);
            for k in [-1, 0, 7, 49, 100] {
                // SAFETY: valid sorted array.
                let r = unsafe { bsearch(&k as *const i32 as _, v.as_ptr() as _, n, 4, cmp_i32) };
                if v.contains(&k) {
                    // SAFETY: `r` points into `v`.
                    assert_eq!(unsafe { *(r as *const i32) }, k);
                } else {
                    assert!(r.is_null());
                }
            }
            // SAFETY: valid array and comparison.
            unsafe { qsort_r(v.as_mut_ptr() as _, n, 4, cmp_rev, ptr::null_mut()) };
            expected.reverse();
            assert_eq!(v, expected);
        }
    }

    #[test]
    fn odd_sizes() {
        #[repr(C, packed)]
        #[derive(Clone, Copy, PartialEq, Debug)]
        struct Rec([u8; 7]);
        unsafe extern "C" fn cmp(a: *const c_void, b: *const c_void) -> c_int {
            // SAFETY: Rec pointers.
            unsafe { (*(a as *const Rec)).0[0] as c_int - (*(b as *const Rec)).0[0] as c_int }
        }
        let mut v: Vec<Rec> = (0..50u8)
            .rev()
            .map(|i| Rec([i, i, i, i, i, i, i]))
            .collect();
        // SAFETY: valid array.
        unsafe { qsort(v.as_mut_ptr() as _, 50, 7, cmp) };
        for (i, r) in v.iter().enumerate() {
            assert_eq!(r.0, [i as u8; 7]);
        }
    }
}
