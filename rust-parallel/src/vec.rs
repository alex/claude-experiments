//! Parallel iterator that moves out of a `Vec<T>`.

use crate::iter::plumbing::{bridge, Consumer, Producer, ProducerCallback, UnindexedConsumer};
use crate::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};
use std::ptr;
use std::slice;

/// Parallel iterator that moves out of a vector.
#[derive(Debug)]
pub struct IntoIter<T: Send> {
    vec: Vec<T>,
}

impl<T: Send> IntoParallelIterator for Vec<T> {
    type Item = T;
    type Iter = IntoIter<T>;

    fn into_par_iter(self) -> Self::Iter {
        IntoIter { vec: self }
    }
}

impl<T: Send> ParallelIterator for IntoIter<T> {
    type Item = T;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn opt_len(&self) -> Option<usize> {
        Some(self.vec.len())
    }
}

impl<T: Send> IndexedParallelIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.vec.len()
    }

    fn drive<C>(self, consumer: C) -> C::Result
    where
        C: Consumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn with_producer<CB>(mut self, callback: CB) -> CB::Output
    where
        CB: ProducerCallback<Self::Item>,
    {
        unsafe {
            // Make the borrow checker happy about aliasing: the vector's
            // length is set to 0 so it no longer "owns" any elements; the
            // producer takes (logical) ownership of them via a raw slice.
            // The allocation itself is still freed by `self.vec`'s Drop
            // after the producer is done.
            let len = self.vec.len();
            self.vec.set_len(0);
            let start = self.vec.as_mut_ptr();
            let slice = slice::from_raw_parts_mut(start, len);
            callback.callback(DrainProducer::new(slice))
        }
    }
}

/// A producer that owns the elements of a `&mut [T]` (they are moved out
/// by `ptr::read`); any elements not consumed are dropped when the
/// producer (or its iterator) is dropped.
pub(crate) struct DrainProducer<'data, T: Send> {
    slice: &'data mut [T],
}

impl<'data, T: 'data + Send> DrainProducer<'data, T> {
    /// Safety: caller asserts ownership of the elements in `slice` (no
    /// other owner will drop or observe them).
    pub(crate) unsafe fn new(slice: &'data mut [T]) -> Self {
        DrainProducer { slice }
    }
}

impl<'data, T: 'data + Send> Producer for DrainProducer<'data, T> {
    type Item = T;
    type IntoIter = SliceDrain<'data, T>;

    fn into_iter(mut self) -> Self::IntoIter {
        // replace the slice so we don't drop it twice
        let slice = std::mem::take(&mut self.slice);
        std::mem::forget(self);
        SliceDrain {
            iter: slice.iter_mut(),
        }
    }

    fn split_at(mut self, index: usize) -> (Self, Self) {
        let slice = std::mem::take(&mut self.slice);
        std::mem::forget(self);
        let (left, right) = slice.split_at_mut(index);
        unsafe { (DrainProducer::new(left), DrainProducer::new(right)) }
    }
}

impl<'data, T: 'data + Send> Drop for DrainProducer<'data, T> {
    fn drop(&mut self) {
        // Drop the elements we still own.
        unsafe { ptr::drop_in_place(self.slice as *mut [T]) };
    }
}

/// Sequential iterator that moves items out of a borrowed slice.
pub(crate) struct SliceDrain<'data, T> {
    iter: slice::IterMut<'data, T>,
}

impl<'data, T: 'data> Iterator for SliceDrain<'data, T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        let ptr: *const T = self.iter.next()?;
        Some(unsafe { ptr::read(ptr) })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.iter.len();
        (len, Some(len))
    }
}

impl<'data, T: 'data> DoubleEndedIterator for SliceDrain<'data, T> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        let ptr: *const T = self.iter.next_back()?;
        Some(unsafe { ptr::read(ptr) })
    }
}

impl<'data, T: 'data> ExactSizeIterator for SliceDrain<'data, T> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<'data, T: 'data> Drop for SliceDrain<'data, T> {
    fn drop(&mut self) {
        // Drop the items we never yielded.
        let iter = std::mem::replace(&mut self.iter, [].iter_mut());
        unsafe { ptr::drop_in_place(iter.into_slice() as *mut [T]) };
    }
}
