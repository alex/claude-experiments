//! Collecting into vectors.
//!
//! Indexed iterators with exact lengths are collected *in place*: the
//! target `Vec`'s spare capacity is carved into disjoint sub-slices,
//! mirroring the producer's splits, and every leaf writes its items
//! directly at their final location (no intermediate buffers, no final
//! copy). Unindexed iterators fall back to per-leaf vectors that are
//! appended at the end.

use std::marker::PhantomData;
use std::mem;
use std::ptr;

use super::noop::NoopReducer;
use super::plumbing::{Consumer, Folder, Reducer, UnindexedConsumer};
use super::{IndexedParallelIterator, IntoParallelIterator, ParallelExtend, ParallelIterator};

/// A `*mut T` that is `Send`; ownership discipline is enforced by the
/// collect protocol (disjoint ranges per consumer).
struct SendPtr<T>(*mut T);

unsafe impl<T: Send> Send for SendPtr<T> {}

impl<T> SendPtr<T> {
    #[inline]
    fn add(&self, offset: usize) -> SendPtr<T> {
        SendPtr(self.0.wrapping_add(offset))
    }
}

impl<T> Copy for SendPtr<T> {}
impl<T> Clone for SendPtr<T> {
    fn clone(&self) -> Self {
        *self
    }
}

/// Collects an exact-length parallel iterator into `target`, replacing
/// its contents (the allocation is reused).
pub fn collect_into_vec<I, T>(pi: I, target: &mut Vec<T>)
where
    I: IndexedParallelIterator<Item = T>,
    T: Send,
{
    target.truncate(0);
    let len = pi.len();
    collect_with_consumer(target, len, |consumer| pi.drive(consumer));
}

/// Collects a parallel iterator whose `opt_len()` returned `Some(len)`
/// (which promises indexed-style driving) into `vec`.
pub(super) fn special_extend<I, T>(pi: I, len: usize, vec: &mut Vec<T>)
where
    I: ParallelIterator<Item = T>,
    T: Send,
{
    collect_with_consumer(vec, len, |consumer| pi.drive_unindexed(consumer));
}

/// Reserves space for `len` more items in `vec`, hands a consumer over
/// that spare capacity to `scope_fn`, checks that every slot was written,
/// and commits the new length.
fn collect_with_consumer<T, F>(vec: &mut Vec<T>, len: usize, scope_fn: F)
where
    T: Send,
    F: FnOnce(CollectConsumer<'_, T>) -> CollectResult<'_, T>,
{
    let start = vec.len();
    vec.reserve(len);

    unsafe {
        let target = vec.as_mut_ptr().add(start);
        let consumer = CollectConsumer::new(target, len);
        // If `scope_fn` panics, `vec` keeps its old length. Completed
        // leaves' `CollectResult`s drop their written items during
        // unwinding; items in a leaf that panicked mid-fold are leaked
        // (memory-safe).
        let result = scope_fn(consumer);
        let total_written = result.len;
        // Release ownership *before* the check so a failed assert doesn't
        // double-drop.
        result.release_ownership();
        assert_eq!(
            total_written, len,
            "expected {len} total writes, but got {total_written}"
        );
        vec.set_len(start + len);
    }
}

pub(super) struct CollectConsumer<'c, T: Send> {
    /// Start of the disjoint target region owned by this consumer.
    start: SendPtr<T>,
    len: usize,
    marker: PhantomData<&'c mut T>,
}

impl<'c, T: Send + 'c> CollectConsumer<'c, T> {
    /// Safety: caller guarantees `[target, target+len)` is valid,
    /// unaliased, uninitialized memory that outlives `'c`.
    unsafe fn new(target: *mut T, len: usize) -> Self {
        CollectConsumer {
            start: SendPtr(target),
            len,
            marker: PhantomData,
        }
    }
}

/// The result of a (sub-)collection: a prefix of a consumer's target
/// range that has been fully written. Owns those written items (drops
/// them if dropped, e.g. during panic unwinding), until ownership is
/// released to the vector at the end.
pub(super) struct CollectResult<'c, T> {
    start: SendPtr<T>,
    total_len: usize,
    /// Number of initialized items, from the start of the range.
    len: usize,
    invariant_lifetime: PhantomData<&'c mut &'c mut [T]>,
}

unsafe impl<'c, T: Send> Send for CollectResult<'c, T> {}

impl<'c, T> CollectResult<'c, T> {
    /// Release ownership of the written items; the caller (the vector)
    /// becomes responsible for dropping them.
    fn release_ownership(mut self) {
        self.len = 0;
        mem::forget(self);
    }
}

impl<'c, T> Drop for CollectResult<'c, T> {
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.start.0, self.len));
        }
    }
}

impl<'c, T: Send + 'c> Consumer<T> for CollectConsumer<'c, T> {
    type Folder = CollectResult<'c, T>;
    type Reducer = CollectReducer;
    type Result = CollectResult<'c, T>;

    fn split_at(self, index: usize) -> (Self, Self, CollectReducer) {
        let CollectConsumer { start, len, .. } = self;
        debug_assert!(index <= len);
        unsafe {
            (
                CollectConsumer::new(start.0, index),
                CollectConsumer::new(start.add(index).0, len - index),
                CollectReducer,
            )
        }
    }

    fn into_folder(self) -> Self::Folder {
        CollectResult {
            start: self.start,
            total_len: self.len,
            len: 0,
            invariant_lifetime: PhantomData,
        }
    }

    fn full(&self) -> bool {
        false
    }
}

impl<'c, T: Send + 'c> Folder<T> for CollectResult<'c, T> {
    type Result = Self;

    #[inline]
    fn consume(mut self, item: T) -> Self {
        assert!(
            self.len < self.total_len,
            "too many values pushed to consumer; expected {}",
            self.total_len
        );
        unsafe {
            ptr::write(self.start.add(self.len).0, item);
        }
        self.len += 1;
        self
    }

    #[inline]
    fn consume_iter<I>(mut self, iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        /// Tracks how many items were written so they are dropped if the
        /// source iterator panics mid-write. For non-panicking sources
        /// LLVM sees `count` is only read on unwind paths and keeps the
        /// hot loop's cursor in a register (this is what lets plain
        /// `map+collect` leaves vectorize).
        struct WriteGuard<T> {
            start: *mut T,
            count: usize,
        }
        impl<T> Drop for WriteGuard<T> {
            fn drop(&mut self) {
                unsafe {
                    ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.start, self.count));
                }
            }
        }

        let mut iter = iter.into_iter();
        let remaining = self.total_len - self.len;
        unsafe {
            let start = self.start.add(self.len).0;
            let mut guard = WriteGuard { start, count: 0 };
            while guard.count < remaining {
                match iter.next() {
                    Some(item) => {
                        start.add(guard.count).write(item);
                        guard.count += 1;
                    }
                    None => break,
                }
            }
            self.len += guard.count;
            mem::forget(guard);
        }
        // Anything left over would overflow our range: mirror `consume`'s
        // bounds panic.
        assert!(
            iter.next().is_none(),
            "too many values pushed to consumer; expected {}",
            self.total_len
        );
        self
    }

    fn complete(self) -> Self::Result {
        // NB: we don't check that the entire range was written here;
        // the reducer and the final length check catch shortfalls.
        self
    }

    fn full(&self) -> bool {
        false
    }
}

/// Combines adjacent `CollectResult`s.
pub(super) struct CollectReducer;

impl<'c, T> Reducer<CollectResult<'c, T>> for CollectReducer {
    fn reduce(
        self,
        mut left: CollectResult<'c, T>,
        right: CollectResult<'c, T>,
    ) -> CollectResult<'c, T> {
        // Merge if the results are adjacent and in left-to-right order;
        // otherwise (a buggy iterator under-filled the left side) drop the
        // right items now -- the final length check will then fail.
        if left.len == left.total_len && left.start.add(left.len).0 == right.start.0 {
            left.total_len += right.total_len;
            left.len += right.len;
            mem::forget(right);
        }
        left
    }
}

impl<'c, T: Send + 'c> UnindexedConsumer<T> for CollectConsumer<'c, T> {
    fn split_off_left(&self) -> Self {
        unreachable!("CollectConsumer must be indexed: `opt_len()` promised an exact length")
    }

    fn to_reducer(&self) -> Self::Reducer {
        CollectReducer
    }
}

// //////////////////////////////////////////////////////////////////////
// Unindexed fallback: per-leaf vectors gathered at the end.

pub(super) struct ListVecConsumer;

pub(super) struct ListVecFolder<T> {
    vec: Vec<T>,
}

impl<T: Send> Consumer<T> for ListVecConsumer {
    type Folder = ListVecFolder<T>;
    type Reducer = ListReducer;
    type Result = std::collections::LinkedList<Vec<T>>;

    fn split_at(self, _index: usize) -> (Self, Self, Self::Reducer) {
        (Self, Self, ListReducer)
    }

    fn into_folder(self) -> Self::Folder {
        ListVecFolder { vec: Vec::new() }
    }

    fn full(&self) -> bool {
        false
    }
}

impl<T: Send> UnindexedConsumer<T> for ListVecConsumer {
    fn split_off_left(&self) -> Self {
        Self
    }

    fn to_reducer(&self) -> Self::Reducer {
        ListReducer
    }
}

impl<T: Send> Folder<T> for ListVecFolder<T> {
    type Result = std::collections::LinkedList<Vec<T>>;

    #[inline]
    fn consume(mut self, item: T) -> Self {
        self.vec.push(item);
        self
    }

    #[inline]
    fn consume_iter<I>(mut self, iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        self.vec.extend(iter);
        self
    }

    fn complete(self) -> Self::Result {
        let mut list = std::collections::LinkedList::new();
        if !self.vec.is_empty() {
            list.push_back(self.vec);
        }
        list
    }

    fn full(&self) -> bool {
        false
    }
}

pub(super) struct ListReducer;

impl<T> Reducer<std::collections::LinkedList<T>> for ListReducer {
    fn reduce(
        self,
        mut left: std::collections::LinkedList<T>,
        mut right: std::collections::LinkedList<T>,
    ) -> std::collections::LinkedList<T> {
        left.append(&mut right);
        left
    }
}

// //////////////////////////////////////////////////////////////////////
// Vec integration

impl<T: Send> ParallelExtend<T> for Vec<T> {
    fn par_extend<I>(&mut self, par_iter: I)
    where
        I: IntoParallelIterator<Item = T>,
    {
        let par_iter = par_iter.into_par_iter();
        match par_iter.opt_len() {
            Some(len) => {
                // Exact length known: write in place, in parallel.
                special_extend(par_iter, len, self);
            }
            None => {
                // Fold into per-leaf vectors, then append them.
                let list = par_iter.drive_unindexed(ListVecConsumer);
                self.reserve(list.iter().map(Vec::len).sum());
                for mut other in list {
                    self.append(&mut other);
                }
            }
        }
    }
}

impl<T: Send> super::FromParallelIterator<T> for Vec<T> {
    fn from_par_iter<I>(par_iter: I) -> Self
    where
        I: IntoParallelIterator<Item = T>,
    {
        let mut vec = Vec::new();
        vec.par_extend(par_iter);
        vec
    }
}

// Marker so `NoopReducer` import isn't unused if features shift around.
#[allow(dead_code)]
fn _noop(_: NoopReducer) {}
