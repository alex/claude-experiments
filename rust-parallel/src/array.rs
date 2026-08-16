//! Parallel iterator over arrays by value (`[T; N]`).

use crate::iter::plumbing::{bridge, Consumer, ProducerCallback, UnindexedConsumer};
use crate::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};
use crate::vec::DrainProducer;
use std::mem::ManuallyDrop;

/// Parallel iterator that moves out of an array.
#[derive(Debug)]
pub struct IntoIter<T: Send, const N: usize> {
    array: [T; N],
}

impl<T: Send, const N: usize> IntoParallelIterator for [T; N] {
    type Item = T;
    type Iter = IntoIter<T, N>;

    fn into_par_iter(self) -> Self::Iter {
        IntoIter { array: self }
    }
}

impl<'a, T: Sync, const N: usize> IntoParallelIterator for &'a [T; N] {
    type Item = &'a T;
    type Iter = crate::slice::Iter<'a, T>;

    fn into_par_iter(self) -> Self::Iter {
        <&[T]>::into_par_iter(self)
    }
}

impl<'a, T: Send, const N: usize> IntoParallelIterator for &'a mut [T; N] {
    type Item = &'a mut T;
    type Iter = crate::slice::IterMut<'a, T>;

    fn into_par_iter(self) -> Self::Iter {
        <&mut [T]>::into_par_iter(self)
    }
}

impl<T: Send, const N: usize> ParallelIterator for IntoIter<T, N> {
    type Item = T;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn opt_len(&self) -> Option<usize> {
        Some(N)
    }
}

impl<T: Send, const N: usize> IndexedParallelIterator for IntoIter<T, N> {
    fn len(&self) -> usize {
        N
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
        unsafe {
            // The `ManuallyDrop` prevents a double drop: ownership of the
            // elements passes to the `DrainProducer` (which drops any it
            // doesn't yield), while the array's storage lives on this
            // stack frame for the duration of the callback.
            let mut array = ManuallyDrop::new(self.array);
            callback.callback(DrainProducer::new(array.as_mut_slice()))
        }
    }
}
