//! Parallel sorting.
//!
//! Unstable sort: a parallel three-way ("fat pivot") quicksort --
//! partitioning is sequential per level but the two recursions run via
//! `join`, and leaves fall back to std's pdqsort. The fat pivot makes
//! heavily-duplicated inputs O(n) instead of quadratic, and a depth
//! limit falls back to sequential sort on adversarial patterns.
//!
//! Stable sort: a parallel merge sort ping-ponging between the slice
//! and an uninitialized scratch buffer. Both the recursive sorts *and*
//! the merges are parallel (merges split via binary search in the
//! larger run). Panic safety (a comparator may panic at any moment) is
//! maintained by three layers of guards -- see the comments on
//! `join_both`, `MergeTailGuard`, `ChildrenGuard` and `MergeToBufGuard`;
//! the invariant is that whenever unwinding escapes a stack frame, the
//! frame's entire sub-range is live in `v` (each element owned exactly
//! once), so the caller's `Vec` can drop normally.

use std::cmp::Ordering;
use std::ptr;
use std::sync::atomic::{AtomicBool, Ordering as AtomicOrdering};

use crate::unwind;

/// Sequential cutoff: below this, std's `sort_unstable_by` is used
/// directly. Chosen so a leaf is a few tens of microseconds of work.
const SORT_SEQ_CUTOFF: usize = 2048;

pub(crate) fn par_quicksort<T, F>(v: &mut [T], compare: F)
where
    T: Send,
    F: Fn(&T, &T) -> Ordering + Sync,
{
    if v.len() <= SORT_SEQ_CUTOFF {
        v.sort_unstable_by(compare);
        return;
    }
    // Standard introsort-style depth limit: 2 * log2(n) + 1.
    let depth_limit = 2 * usize::BITS - 2 * v.len().leading_zeros() + 1;
    quick_recurse(v, &compare, None, depth_limit);
}

/// Parallel pdqsort-style recursion. `pred` is the element just before
/// this sub-slice in the final order (everything in `v` is >= it);
/// when the chosen pivot equals `pred`, the range has many duplicates of
/// that value and we strip them with a single equal-partition pass
/// instead of degenerating.
fn quick_recurse<T, F>(
    mut v: &mut [T],
    compare: &F,
    mut pred: Option<&mut T>,
    mut depth_limit: u32,
) where
    T: Send,
    F: Fn(&T, &T) -> Ordering + Sync,
{
    loop {
        if v.len() <= SORT_SEQ_CUTOFF {
            v.sort_unstable_by(compare);
            return;
        }
        if depth_limit == 0 {
            // Pathological pivot pattern: bail out to std's pdqsort.
            v.sort_unstable_by(compare);
            return;
        }
        depth_limit -= 1;

        let pivot_idx = choose_pivot(v, compare);

        // Duplicate run: pivot equal to the predecessor means everything
        // <= pivot in this range IS the pivot value.
        if let Some(p) = &pred {
            if compare(p, &v[pivot_idx]) != Ordering::Less {
                let mid = partition_equal(v, pivot_idx, compare);
                v = &mut v[mid..];
                continue;
            }
        }

        let mid = partition(v, pivot_idx, compare);
        let (left, rest) = v.split_at_mut(mid);
        let (pivot_slice, right) = rest.split_at_mut(1);
        let right_pred = Some(&mut pivot_slice[0]);
        let left_pred = pred.take();
        crate::join(
            || quick_recurse(left, compare, left_pred, depth_limit),
            || quick_recurse(right, compare, right_pred, depth_limit),
        );
        return;
    }
}

/// Moves the pivot (at `pivot_idx`) aside and partitions the rest with
/// the branchless block algorithm; returns the pivot's final position.
/// After return: `v[..mid] < pivot`, `v[mid] == pivot`, `v[mid+1..] >=
/// pivot`.
fn partition<T, F>(v: &mut [T], pivot_idx: usize, compare: &F) -> usize
where
    F: Fn(&T, &T) -> Ordering,
{
    v.swap(0, pivot_idx);
    let (pivot_slot, rest) = v.split_at_mut(1);

    // Read the pivot into a stack copy so comparisons don't alias the
    // slice; the guard writes it back even if a comparison panics.
    let mut tmp = std::mem::ManuallyDrop::new(unsafe { ptr::read(&pivot_slot[0]) });
    let write_back = WriteBackOnDrop {
        src: &mut *tmp,
        dest: pivot_slot.as_mut_ptr(),
    };
    let pivot: &T = unsafe { &*write_back.src };

    let mid = partition_in_blocks(rest, pivot, &|a, b| compare(a, b) == Ordering::Less);

    drop(write_back); // restore pivot into v[0]
    v.swap(0, mid);
    mid
}

struct WriteBackOnDrop<T> {
    src: *mut T,
    dest: *mut T,
}

impl<T> Drop for WriteBackOnDrop<T> {
    fn drop(&mut self) {
        unsafe { ptr::copy_nonoverlapping(self.src, self.dest, 1) }
    }
}

/// Partitions `v` so that elements equal to the pivot (at `pivot_idx`)
/// come first; returns how many there are. Everything in `v` is known
/// to be >= the pivot value.
fn partition_equal<T, F>(v: &mut [T], pivot_idx: usize, compare: &F) -> usize
where
    F: Fn(&T, &T) -> Ordering,
{
    v.swap(0, pivot_idx);
    let (pivot_slot, rest) = v.split_at_mut(1);
    let mut tmp = std::mem::ManuallyDrop::new(unsafe { ptr::read(&pivot_slot[0]) });
    let write_back = WriteBackOnDrop {
        src: &mut *tmp,
        dest: pivot_slot.as_mut_ptr(),
    };
    let pivot: &T = unsafe { &*write_back.src };

    let len = rest.len();
    let mut l = 0;
    let mut r = len;
    loop {
        // Elements NOT greater than the pivot are equal to it (all are >=).
        while l < r && compare(pivot, &rest[l]) != Ordering::Less {
            l += 1;
        }
        while l < r && compare(pivot, &rest[r - 1]) == Ordering::Less {
            r -= 1;
        }
        if l >= r {
            break;
        }
        rest.swap(l, r - 1);
        l += 1;
        r -= 1;
    }
    drop(write_back);
    l + 1 // include the pivot itself
}

/// Median of 9 (three medians-of-3) for large slices, median of 3
/// otherwise.
fn choose_pivot<T, F>(v: &[T], compare: &F) -> usize
where
    F: Fn(&T, &T) -> Ordering,
{
    let len = v.len();
    let median3 = |a: usize, b: usize, c: usize| -> usize {
        let ab = compare(&v[a], &v[b]) == Ordering::Less;
        let bc = compare(&v[b], &v[c]) == Ordering::Less;
        let ac = compare(&v[a], &v[c]) == Ordering::Less;
        match (ab, bc, ac) {
            (true, true, _) => b,
            (true, false, true) => c,
            (true, false, false) => a,
            (false, true, true) => a,
            (false, true, false) => c,
            (false, false, _) => b,
        }
    };
    if len >= 8192 {
        let eighth = len / 8;
        let a = median3(0, eighth, 2 * eighth);
        let b = median3(3 * eighth, 4 * eighth, 5 * eighth);
        let c = median3(6 * eighth, 7 * eighth, len - 1);
        median3(a, b, c)
    } else {
        median3(0, len / 2, len - 1)
    }
}

/// Branchless block partition (BlockQuicksort, as used by std/pdqsort):
/// scans 128-element blocks from both ends recording out-of-place
/// offsets in stack buffers with branch-free writes, then swaps the
/// misplaced pairs with a cyclic permutation. Returns the number of
/// elements less than the pivot.
fn partition_in_blocks<T, F>(v: &mut [T], pivot: &T, is_less: &F) -> usize
where
    F: Fn(&T, &T) -> bool,
{
    const BLOCK: usize = 128;

    let mut l = v.as_mut_ptr();
    let mut block_l = BLOCK;
    let mut start_l = ptr::null_mut::<u8>();
    let mut end_l = ptr::null_mut::<u8>();
    let mut offsets_l = [std::mem::MaybeUninit::<u8>::uninit(); BLOCK];

    // `r` is one-past-the-end of the unprocessed region.
    let mut r = unsafe { l.add(v.len()) };
    let mut block_r = BLOCK;
    let mut start_r = ptr::null_mut::<u8>();
    let mut end_r = ptr::null_mut::<u8>();
    let mut offsets_r = [std::mem::MaybeUninit::<u8>::uninit(); BLOCK];

    fn width<T>(l: *mut T, r: *mut T) -> usize {
        unsafe { r.offset_from(l) as usize }
    }

    loop {
        let is_done = width(l, r) <= 2 * BLOCK;

        if is_done {
            // Split the remaining region between the two blocks, keeping
            // any block that still has pending offsets at full size.
            let mut rem = width(l, r);
            if start_l < end_l || start_r < end_r {
                rem -= BLOCK;
            }
            if start_l < end_l {
                block_r = rem;
            } else if start_r < end_r {
                block_l = rem;
            } else {
                block_l = rem / 2;
                block_r = rem - block_l;
            }
            debug_assert!(block_l <= BLOCK && block_r <= BLOCK);
        }

        if start_l == end_l {
            // Record offsets of elements that must move right (>= pivot).
            start_l = offsets_l.as_mut_ptr() as *mut u8;
            end_l = start_l;
            let mut elem = l;
            for i in 0..block_l {
                unsafe {
                    end_l.write(i as u8);
                    end_l = end_l.add(!is_less(&*elem, pivot) as usize);
                    elem = elem.add(1);
                }
            }
        }

        if start_r == end_r {
            // Record offsets of elements that must move left (< pivot).
            start_r = offsets_r.as_mut_ptr() as *mut u8;
            end_r = start_r;
            let mut elem = r;
            for i in 0..block_r {
                unsafe {
                    elem = elem.sub(1);
                    end_r.write(i as u8);
                    end_r = end_r.add(is_less(&*elem, pivot) as usize);
                }
            }
        }

        // Swap the out-of-place pairs with one cyclic permutation.
        let count = Ord::min(width(start_l, end_l), width(start_r, end_r));
        if count > 0 {
            macro_rules! left {
                () => {
                    l.add(*start_l as usize)
                };
            }
            macro_rules! right {
                () => {
                    r.sub(*start_r as usize + 1)
                };
            }
            unsafe {
                let tmp = ptr::read(left!());
                ptr::copy_nonoverlapping(right!(), left!(), 1);
                for _ in 1..count {
                    start_l = start_l.add(1);
                    ptr::copy_nonoverlapping(left!(), right!(), 1);
                    start_r = start_r.add(1);
                    ptr::copy_nonoverlapping(right!(), left!(), 1);
                }
                ptr::copy_nonoverlapping(&tmp, right!(), 1);
                std::mem::forget(tmp);
                start_l = start_l.add(1);
                start_r = start_r.add(1);
            }
        }

        if start_l == end_l {
            l = unsafe { l.add(block_l) };
        }
        if start_r == end_r {
            r = unsafe { r.sub(block_r) };
        }

        if is_done {
            break;
        }
    }

    // At most one side still has offsets: those elements sit in the wrong
    // half with no partners; move them to the boundary one by one.
    if start_l < end_l {
        debug_assert_eq!(width(l, r), block_l);
        while start_l < end_l {
            unsafe {
                end_l = end_l.sub(1);
                ptr::swap(l.add(*end_l as usize), r.sub(1));
                r = r.sub(1);
            }
        }
        width(v.as_mut_ptr(), r)
    } else if start_r < end_r {
        debug_assert_eq!(width(l, r), block_r);
        while start_r < end_r {
            unsafe {
                end_r = end_r.sub(1);
                ptr::swap(l, r.sub(*end_r as usize + 1));
                l = l.add(1);
            }
        }
        width(v.as_mut_ptr(), l)
    } else {
        width(v.as_mut_ptr(), l)
    }
}

// //////////////////////////////////////////////////////////////////////
// Stable parallel merge sort

/// Sequential cutoff for the stable sort's leaves.
const STABLE_SEQ_CUTOFF: usize = 4096;
/// Below this many total elements a merge is done sequentially.
const MERGE_SEQ_CUTOFF: usize = 8192;

/// A `*mut T` usable from multiple closures (disjoint ranges only).
struct SendPtr<T>(*mut T);
unsafe impl<T: Send> Send for SendPtr<T> {}
unsafe impl<T: Send> Sync for SendPtr<T> {}
impl<T> Copy for SendPtr<T> {}
impl<T> Clone for SendPtr<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> SendPtr<T> {
    #[inline]
    fn get(self) -> *mut T {
        self.0
    }
}

/// Like `join`, but guarantees BOTH closures run to completion even if
/// one panics (panics are re-thrown afterwards, first one wins). The
/// sort's ownership-restoration guards rely on "no sub-task is ever
/// abandoned unexecuted".
fn join_both<A, B>(oper_a: A, oper_b: B)
where
    A: FnOnce() + Send,
    B: FnOnce() + Send,
{
    let (result_a, result_b) = crate::join(
        || unwind::halt_unwinding(oper_a),
        || unwind::halt_unwinding(oper_b),
    );
    if let Err(payload) = result_a {
        unwind::resume_unwinding(payload);
    }
    if let Err(payload) = result_b {
        unwind::resume_unwinding(payload);
    }
}

pub(crate) fn par_mergesort<T, F>(v: &mut [T], compare: F)
where
    T: Send,
    F: Fn(&T, &T) -> Ordering + Sync,
{
    let len = v.len();
    if len <= STABLE_SEQ_CUTOFF {
        v.sort_by(compare);
        return;
    }
    // Uninitialized scratch storage. `buf`'s length stays 0, so it never
    // drops elements: `v` (the caller's storage) is always the sole
    // dropper, and the guards below keep "every element bitwise-live in
    // v exactly once" true whenever unwinding escapes.
    let mut buf: Vec<T> = Vec::with_capacity(len);
    let buf_ptr = SendPtr(buf.as_mut_ptr());
    stable_recurse(v, buf_ptr, true, &compare);
}

/// Recursive sort. Postcondition on success: the sorted range lives in
/// `v` if `in_place`, or in `buf[0..v.len()]` otherwise (with `v` then
/// containing stale bits). Postcondition on unwind: everything lives in
/// `v`.
fn stable_recurse<T, F>(v: &mut [T], buf: SendPtr<T>, in_place: bool, compare: &F)
where
    T: Send,
    F: Fn(&T, &T) -> Ordering + Sync,
{
    let len = v.len();

    if len <= STABLE_SEQ_CUTOFF {
        v.sort_by(compare);
        if !in_place {
            unsafe {
                ptr::copy_nonoverlapping(v.as_ptr(), buf.get(), len);
            }
        }
        return;
    }

    let mid = len / 2;

    // ---- Phase 1: sort the two halves (into the opposite buffer). ----
    let v_ptr = SendPtr(v.as_mut_ptr());
    let flags = (AtomicBool::new(false), AtomicBool::new(false));
    {
        let guard = ChildrenGuard {
            v: v_ptr,
            buf,
            mid,
            len,
            flags: &flags,
        };
        let child_in_place = !in_place;
        let buf_right = SendPtr(unsafe { buf.get().add(mid) });
        let (flag_left, flag_right) = (&flags.0, &flags.1);
        let compare_ref = &compare;
        join_both(
            move || {
                let left = unsafe { std::slice::from_raw_parts_mut(v_ptr.get(), mid) };
                stable_recurse(left, buf, child_in_place, *compare_ref);
                if !child_in_place {
                    flag_left.store(true, AtomicOrdering::Release);
                }
            },
            move || {
                let right =
                    unsafe { std::slice::from_raw_parts_mut(v_ptr.get().add(mid), len - mid) };
                stable_recurse(right, buf_right, child_in_place, *compare_ref);
                if !child_in_place {
                    flag_right.store(true, AtomicOrdering::Release);
                }
            },
        );
        // Success: both halves are where the merge below expects them;
        // the guard must not copy anything back.
        std::mem::forget(guard);
    }

    // ---- Phase 2: merge the halves into the requested destination. ----
    unsafe {
        if in_place {
            // Halves live in buf; merge into v. If the merge panics, the
            // seq-merge tail guards (plus join_both) guarantee v's range
            // is fully written before unwinding escapes -- v is live.
            par_merge(
                buf.get(),
                mid,
                buf.get().add(mid),
                len - mid,
                v_ptr.get(),
                compare,
            );
        } else {
            // Halves live in v; merge into buf. On unwind the merged
            // data (fully written into buf by the tail guards) must be
            // restored to v.
            let guard = MergeToBufGuard {
                v: v_ptr,
                buf,
                len,
            };
            par_merge(v_ptr.get(), mid, v_ptr.get().add(mid), len - mid, buf.get(), compare);
            std::mem::forget(guard);
        }
    }
}

/// Restores `v` ownership if phase 1 unwinds: any half whose flag says
/// "sorted copy is in buf" is copied back over its (stale) v range.
struct ChildrenGuard<'a, T> {
    v: SendPtr<T>,
    buf: SendPtr<T>,
    mid: usize,
    len: usize,
    flags: &'a (AtomicBool, AtomicBool),
}

impl<'a, T> Drop for ChildrenGuard<'a, T> {
    fn drop(&mut self) {
        unsafe {
            if self.flags.0.load(AtomicOrdering::Acquire) {
                ptr::copy_nonoverlapping(self.buf.get(), self.v.get(), self.mid);
            }
            if self.flags.1.load(AtomicOrdering::Acquire) {
                ptr::copy_nonoverlapping(
                    self.buf.get().add(self.mid),
                    self.v.get().add(self.mid),
                    self.len - self.mid,
                );
            }
        }
    }
}

/// Restores `v` ownership if a merge-into-buf unwinds (the tail guards
/// have already made `buf[0..len]` fully initialized by then).
struct MergeToBufGuard<T> {
    v: SendPtr<T>,
    buf: SendPtr<T>,
    len: usize,
}

impl<T> Drop for MergeToBufGuard<T> {
    fn drop(&mut self) {
        unsafe {
            ptr::copy_nonoverlapping(self.buf.get(), self.v.get(), self.len);
        }
    }
}

/// Parallel merge of two sorted runs `a` (left) and `b` (right) into
/// `dst`. All regions are disjoint. Splits the larger run at its
/// midpoint and binary-searches the split point in the smaller run;
/// stability is preserved by the tie-breaking rules in the split and in
/// `seq_merge`.
///
/// Safety: caller guarantees `a`/`b` are initialized sorted runs, `dst`
/// has room for `a_len + b_len`, and all three ranges are disjoint.
unsafe fn par_merge<T, F>(
    a: *mut T,
    a_len: usize,
    b: *mut T,
    b_len: usize,
    dst: *mut T,
    compare: &F,
) where
    T: Send,
    F: Fn(&T, &T) -> Ordering + Sync,
{
    if a_len + b_len <= MERGE_SEQ_CUTOFF {
        seq_merge(a, a_len, b, b_len, dst, compare);
        return;
    }

    // Split point (ma, mb): left sub-merge gets a[..ma] + b[..mb].
    let (ma, mb) = if a_len >= b_len {
        let ma = a_len / 2;
        let pivot = &*a.add(ma);
        // b elements strictly less than the pivot go left; equal ones
        // stay right so that a's equals (left run) precede them.
        let mb = lower_bound(b, b_len, |x| compare(x, pivot) == Ordering::Less);
        (ma, mb)
    } else {
        let mb = b_len / 2;
        let pivot = &*b.add(mb);
        // a elements less-or-equal go left: the left run's equals must
        // precede the pivot.
        let ma = lower_bound(a, a_len, |x| compare(x, pivot) != Ordering::Greater);
        (ma, mb)
    };

    let (a_p, b_p, dst_p) = (SendPtr(a), SendPtr(b), SendPtr(dst));
    join_both(
        move || unsafe {
            par_merge(a_p.get(), ma, b_p.get(), mb, dst_p.get(), compare);
        },
        move || unsafe {
            par_merge(
                a_p.get().add(ma),
                a_len - ma,
                b_p.get().add(mb),
                b_len - mb,
                dst_p.get().add(ma + mb),
                compare,
            );
        },
    );
}

/// Number of leading elements satisfying `pred` (which must be
/// monotone: true-prefix, false-suffix).
unsafe fn lower_bound<T, P>(base: *const T, len: usize, pred: P) -> usize
where
    P: Fn(&T) -> bool,
{
    let mut lo = 0usize;
    let mut hi = len;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if pred(&*base.add(mid)) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

/// Sequential stable merge. The tail guard moves any remaining source
/// elements into the remaining destination slots -- on the normal path
/// (one run exhausted) *and* if `compare` panics, so `dst` is fully
/// initialized in all cases.
unsafe fn seq_merge<T, F>(a: *mut T, a_len: usize, b: *mut T, b_len: usize, dst: *mut T, compare: &F)
where
    F: Fn(&T, &T) -> Ordering,
{
    struct MergeTailGuard<T> {
        a: *mut T,
        a_end: *mut T,
        b: *mut T,
        b_end: *mut T,
        dst: *mut T,
    }
    impl<T> Drop for MergeTailGuard<T> {
        fn drop(&mut self) {
            unsafe {
                let a_rem = self.a_end.offset_from(self.a) as usize;
                ptr::copy_nonoverlapping(self.a, self.dst, a_rem);
                let b_rem = self.b_end.offset_from(self.b) as usize;
                ptr::copy_nonoverlapping(self.b, self.dst.add(a_rem), b_rem);
            }
        }
    }

    let mut guard = MergeTailGuard {
        a,
        a_end: a.add(a_len),
        b,
        b_end: b.add(b_len),
        dst,
    };
    while guard.a < guard.a_end && guard.b < guard.b_end {
        // Take from the left run on ties: stability.
        if compare(&*guard.b, &*guard.a) == Ordering::Less {
            ptr::copy_nonoverlapping(guard.b, guard.dst, 1);
            guard.b = guard.b.add(1);
        } else {
            ptr::copy_nonoverlapping(guard.a, guard.dst, 1);
            guard.a = guard.a.add(1);
        }
        guard.dst = guard.dst.add(1);
    }
    // Guard drop copies whichever tail remains.
}
