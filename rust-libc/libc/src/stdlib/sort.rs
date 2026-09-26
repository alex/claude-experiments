//! `qsort`, `qsort_r` and `bsearch`.
//!
//! `qsort` is an allocation-free **introsort**: quicksort with a
//! median-of-three pivot and three-way partitioning (so runs of equal
//! keys cost nothing), insertion sort for short ranges, recursion only
//! into the smaller side (so the stack stays `O(log n)`), and a fall back
//! to heapsort once the recursion depth exceeds `2 log2 n`, which bounds
//! the worst case at `O(n log n)` however adversarial the input or the
//! comparison function.

use core::ffi::{c_int, c_void};
use core::ptr;

type Cmp = unsafe extern "C" fn(*const c_void, *const c_void) -> c_int;
type CmpR = unsafe extern "C" fn(*const c_void, *const c_void, *mut c_void) -> c_int;

/// Ranges of at most this many elements are insertion sorted.
const INSERTION_LIMIT: usize = 16;

/// Swaps two elements of `size` bytes.
///
/// # Safety
/// Both pointers must be valid for `size` bytes and not overlap.
#[inline(always)]
unsafe fn swap(a: *mut u8, b: *mut u8, size: usize) {
    // SAFETY: caller contract.
    unsafe {
        match size {
            4 => {
                let x = ptr::read_unaligned(a as *const u32);
                ptr::write_unaligned(a as *mut u32, ptr::read_unaligned(b as *const u32));
                ptr::write_unaligned(b as *mut u32, x);
            }
            8 => {
                let x = ptr::read_unaligned(a as *const u64);
                ptr::write_unaligned(a as *mut u64, ptr::read_unaligned(b as *const u64));
                ptr::write_unaligned(b as *mut u64, x);
            }
            _ => {
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
    cmp: &mut impl FnMut(*const u8, *const u8) -> c_int,
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

/// Insertion sort of `n` elements.
///
/// # Safety
/// `base` must be valid for `n * size` bytes.
unsafe fn insertion_sort(
    base: *mut u8,
    n: usize,
    size: usize,
    cmp: &mut impl FnMut(*const u8, *const u8) -> c_int,
) {
    // SAFETY: all indices are below `n`.
    let at = |i: usize| unsafe { base.add(i * size) };
    for i in 1..n {
        let mut j = i;
        while j > 0 && cmp(at(j - 1), at(j)) > 0 {
            // SAFETY: distinct elements inside the array.
            unsafe { swap(at(j - 1), at(j), size) };
            j -= 1;
        }
    }
}

/// Introsort of `n` elements; `depth` is the remaining quicksort depth.
///
/// # Safety
/// `base` must be valid for `n * size` bytes.
unsafe fn introsort(
    mut base: *mut u8,
    mut n: usize,
    size: usize,
    cmp: &mut impl FnMut(*const u8, *const u8) -> c_int,
    mut depth: u32,
) {
    loop {
        if n <= INSERTION_LIMIT {
            // SAFETY: forwarded.
            unsafe { insertion_sort(base, n, size, cmp) };
            return;
        }
        if depth == 0 {
            // SAFETY: forwarded.
            unsafe { heapsort(base, n, size, cmp) };
            return;
        }
        depth -= 1;
        // SAFETY: all indices are below `n`.
        let at = |i: usize| unsafe { base.add(i * size) };
        // Median of three into position 0.
        let mid = n / 2;
        // SAFETY: distinct elements inside the array.
        unsafe {
            if cmp(at(mid), at(0)) < 0 {
                swap(at(mid), at(0), size);
            }
            if cmp(at(n - 1), at(mid)) < 0 {
                swap(at(n - 1), at(mid), size);
                if cmp(at(mid), at(0)) < 0 {
                    swap(at(mid), at(0), size);
                }
            }
            swap(at(0), at(mid), size);
        }
        // Three-way partition around the pivot at 0:
        // [1, lt) < pivot, [lt, i) == pivot, [gt, n) > pivot.
        let (mut lt, mut i, mut gt) = (1usize, 1usize, n);
        while i < gt {
            let c = cmp(at(i), at(0));
            if c < 0 {
                if lt != i {
                    // SAFETY: distinct positions inside the array.
                    unsafe { swap(at(lt), at(i), size) };
                }
                lt += 1;
                i += 1;
            } else if c > 0 {
                gt -= 1;
                if i != gt {
                    // SAFETY: distinct positions inside the array.
                    unsafe { swap(at(i), at(gt), size) };
                }
            } else {
                i += 1;
            }
        }
        // Move the pivot to the end of the "less" run.
        lt -= 1;
        if lt != 0 {
            // SAFETY: distinct positions inside the array.
            unsafe { swap(at(0), at(lt), size) };
        }
        // Recurse into the smaller side, iterate on the larger.
        let (left_n, right_n) = (lt, n - gt);
        if left_n < right_n {
            // SAFETY: a sub-range of the array.
            unsafe { introsort(base, left_n, size, cmp, depth) };
            base = at(gt);
            n = right_n;
        } else {
            // SAFETY: a sub-range of the array.
            unsafe { introsort(at(gt), right_n, size, cmp, depth) };
            n = left_n;
        }
    }
}

/// Sorts with [`introsort`], given a comparison closure.
///
/// # Safety
/// `base` must be valid for `n * size` bytes.
unsafe fn sort(
    base: *mut u8,
    n: usize,
    size: usize,
    mut cmp: impl FnMut(*const u8, *const u8) -> c_int,
) {
    if size == 0 {
        return;
    }
    let depth = 2 * (usize::BITS - n.leading_zeros());
    // SAFETY: forwarded.
    unsafe { introsort(base, n, size, &mut cmp, depth) }
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
        sort(base as *mut u8, n, size, |a, b| {
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
        sort(base as *mut u8, n, size, |a, b| {
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
    fn large_sorted_reversed_and_equal() {
        for n in [17usize, 100, 5000, 100_000] {
            let mut seed = 7u32;
            let cases: [Vec<i32>; 5] = [
                (0..n as i32).collect(),
                (0..n as i32).rev().collect(),
                core::iter::repeat_n(42, n).collect(),
                (0..n as i32).map(|i| i % 3).collect(),
                (0..n)
                    .map(|_| {
                        seed = seed.wrapping_mul(1103515245).wrapping_add(12345);
                        (seed >> 8) as i32
                    })
                    .collect(),
            ];
            for mut v in cases {
                let mut expected = v.clone();
                expected.sort();
                // SAFETY: valid array and comparison.
                unsafe { qsort(v.as_mut_ptr() as _, n, 4, cmp_i32) };
                assert_eq!(v, expected);
            }
        }
        // An inconsistent comparison function must still terminate.
        unsafe extern "C" fn bad(_: *const c_void, _: *const c_void) -> c_int {
            1
        }
        let mut v: Vec<i32> = (0..3000).collect();
        // SAFETY: valid array; the comparison is garbage but safe.
        unsafe { qsort(v.as_mut_ptr() as _, v.len(), 4, bad) };
        let mut sorted = v.clone();
        sorted.sort();
        assert_eq!(sorted, (0..3000).collect::<Vec<_>>()); // still a permutation
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
