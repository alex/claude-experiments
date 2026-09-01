//! Parallel iterators over `Range<T>` and `RangeInclusive<T>` for
//! primitive integer types and `char`.

use crate::iter::plumbing::{
    bridge, bridge_unindexed, Consumer, Folder, Producer, ProducerCallback, UnindexedConsumer,
    UnindexedProducer,
};
use crate::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};
use std::ops::{Range, RangeInclusive};

/// Parallel iterator over a `Range<T>`.
#[derive(Debug, Clone)]
pub struct RangeIter<T> {
    range: Range<T>,
}

impl<T> IntoParallelIterator for Range<T>
where
    RangeIter<T>: ParallelIterator,
{
    type Item = <RangeIter<T> as ParallelIterator>::Item;
    type Iter = RangeIter<T>;

    fn into_par_iter(self) -> Self::Iter {
        RangeIter { range: self }
    }
}

/// Implemented for all primitive integer types; for `u64`/`i64` (where
/// std's `Range` is not `ExactSizeIterator`) a custom exact-size
/// sequential iterator is used, so even those ranges are fully indexed
/// (lengths above `usize::MAX` panic, as with rayon).
macro_rules! indexed_range_impl {
    ( $t:ty, $iter:ty, $to_iter:expr ) => {
        impl ParallelIterator for RangeIter<$t> {
            type Item = $t;

            fn drive_unindexed<C>(self, consumer: C) -> C::Result
            where
                C: UnindexedConsumer<Self::Item>,
            {
                bridge(self, consumer)
            }

            fn opt_len(&self) -> Option<usize> {
                Some(self.len())
            }
        }

        impl IndexedParallelIterator for RangeIter<$t> {
            fn len(&self) -> usize {
                range_len_usize(&self.range)
            }

            fn drive<C>(self, consumer: C) -> C::Result
            where
                C: Consumer<Self::Item>,
            {
                bridge(self, consumer)
            }

            fn with_producer<CB>(self, callback: CB) -> CB::Output
            where
                CB: ProducerCallback<Self::Item>,
            {
                callback.callback(RangeProducer { range: self.range })
            }
        }

        impl Producer for RangeProducer<$t> {
            type Item = $t;
            type IntoIter = $iter;

            #[inline]
            fn into_iter(self) -> Self::IntoIter {
                ($to_iter)(self.range)
            }

            #[inline]
            fn split_at(self, index: usize) -> (Self, Self) {
                let mid = self.range.start.wrapping_add(index as $t);
                (
                    RangeProducer {
                        range: self.range.start..mid,
                    },
                    RangeProducer {
                        range: mid..self.range.end,
                    },
                )
            }
        }
    };
}

struct RangeProducer<T> {
    range: Range<T>,
}

trait RangeLen {
    fn range_len(range: &Range<Self>) -> u128
    where
        Self: Sized;
}

macro_rules! range_len_impl {
    ( $t:ty ) => {
        impl RangeLen for $t {
            #[inline]
            fn range_len(range: &Range<Self>) -> u128 {
                if range.start < range.end {
                    (range.end as i128 - range.start as i128) as u128
                } else {
                    0
                }
            }
        }
    };
}

range_len_impl!(u8);
range_len_impl!(u16);
range_len_impl!(u32);
range_len_impl!(u64);
range_len_impl!(usize);
range_len_impl!(i8);
range_len_impl!(i16);
range_len_impl!(i32);
range_len_impl!(i64);
range_len_impl!(isize);

#[inline]
fn range_len_usize<T: RangeLen>(range: &Range<T>) -> usize {
    let len = T::range_len(range);
    usize::try_from(len).expect("parallel range length exceeds usize::MAX")
}

indexed_range_impl!(u8, Range<u8>, |r| r);
indexed_range_impl!(u16, Range<u16>, |r| r);
indexed_range_impl!(u32, Range<u32>, |r| r);
indexed_range_impl!(u64, ExactRange<u64>, ExactRange::new);
indexed_range_impl!(usize, Range<usize>, |r| r);
indexed_range_impl!(i8, Range<i8>, |r| r);
indexed_range_impl!(i16, Range<i16>, |r| r);
indexed_range_impl!(i32, Range<i32>, |r| r);
indexed_range_impl!(i64, ExactRange<i64>, ExactRange::new);
indexed_range_impl!(isize, Range<isize>, |r| r);

/// Exact-size sequential range iterator for 64-bit types, where std's
/// `Range` does not implement `ExactSizeIterator`. Only constructed by
/// producers, whose total length was already validated to fit `usize`.
#[derive(Debug, Clone)]
pub struct ExactRange<T> {
    range: Range<T>,
}

impl<T> ExactRange<T> {
    fn new(range: Range<T>) -> Self {
        ExactRange { range }
    }
}

macro_rules! exact_range_impl {
    ( $t:ty ) => {
        impl Iterator for ExactRange<$t> {
            type Item = $t;

            #[inline]
            fn next(&mut self) -> Option<$t> {
                self.range.next()
            }

            #[inline]
            fn size_hint(&self) -> (usize, Option<usize>) {
                let len = range_len_usize(&self.range);
                (len, Some(len))
            }

            #[inline]
            fn fold<B, F>(self, init: B, f: F) -> B
            where
                F: FnMut(B, $t) -> B,
            {
                self.range.fold(init, f)
            }
        }

        impl DoubleEndedIterator for ExactRange<$t> {
            #[inline]
            fn next_back(&mut self) -> Option<$t> {
                self.range.next_back()
            }
        }

        impl ExactSizeIterator for ExactRange<$t> {
            #[inline]
            fn len(&self) -> usize {
                range_len_usize(&self.range)
            }
        }
    };
}

exact_range_impl!(u64);
exact_range_impl!(i64);

// //////////////////////////////////////////////////////////////////////
// RangeInclusive

/// Parallel iterator over a `RangeInclusive<T>`.
#[derive(Debug, Clone)]
pub struct RangeInclusiveIter<T> {
    start: T,
    end: T,
    exhausted: bool,
}

impl<T: Copy + PartialOrd> IntoParallelIterator for RangeInclusive<T>
where
    RangeInclusiveIter<T>: ParallelIterator,
{
    type Item = <RangeInclusiveIter<T> as ParallelIterator>::Item;
    type Iter = RangeInclusiveIter<T>;

    fn into_par_iter(self) -> Self::Iter {
        let exhausted = self.is_empty();
        let (start, end) = self.into_inner();
        RangeInclusiveIter {
            start,
            end,
            exhausted,
        }
    }
}

/// Inclusive ranges are driven as *unindexed* iterators (splitting at the
/// midpoint), which sidesteps the `T::MAX` length-overflow problem while
/// still parallelizing well: splits are still perfectly balanced.
macro_rules! unindexed_inclusive_range_impl {
    ( $t:ty ) => {
        impl ParallelIterator for RangeInclusiveIter<$t> {
            type Item = $t;

            fn drive_unindexed<C>(self, consumer: C) -> C::Result
            where
                C: UnindexedConsumer<Self::Item>,
            {
                if self.exhausted {
                    consumer.into_folder().complete()
                } else {
                    bridge_unindexed(self, consumer)
                }
            }
        }

        impl UnindexedProducer for RangeInclusiveIter<$t> {
            type Item = $t;

            fn split(self) -> (Self, Option<Self>) {
                if self.start >= self.end {
                    return (self, None);
                }
                // midpoint without overflow
                let mid = self.start + (self.end - self.start) / 2;
                let right_start = mid + 1;
                (
                    RangeInclusiveIter {
                        start: self.start,
                        end: mid,
                        exhausted: false,
                    },
                    Some(RangeInclusiveIter {
                        start: right_start,
                        end: self.end,
                        exhausted: false,
                    }),
                )
            }

            fn fold_with<F>(self, folder: F) -> F
            where
                F: Folder<Self::Item>,
            {
                folder.consume_iter(self.start..=self.end)
            }
        }
    };
}

unindexed_inclusive_range_impl!(u8);
unindexed_inclusive_range_impl!(u16);
unindexed_inclusive_range_impl!(u32);
unindexed_inclusive_range_impl!(u64);
unindexed_inclusive_range_impl!(usize);
unindexed_inclusive_range_impl!(i8);
unindexed_inclusive_range_impl!(i16);
unindexed_inclusive_range_impl!(i32);
unindexed_inclusive_range_impl!(i64);
unindexed_inclusive_range_impl!(isize);
