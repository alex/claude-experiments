//! Parallel iterators over slices (`&[T]`, `&mut [T]`) and the
//! [`ParallelSlice`]/[`ParallelSliceMut`] extension traits (`par_chunks`,
//! `par_windows`, ...).

use crate::iter::plumbing::{bridge, Consumer, Producer, ProducerCallback, UnindexedConsumer};
use crate::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};

/// Parallel extensions for slices.
pub trait ParallelSlice<T: Sync> {
    /// Returns the slice (implementation detail).
    fn as_parallel_slice(&self) -> &[T];

    /// Parallel iterator over non-overlapping chunks of `chunk_size`
    /// items (the last chunk may be shorter).
    fn par_chunks(&self, chunk_size: usize) -> Chunks<'_, T> {
        assert!(chunk_size != 0, "chunk_size must not be zero");
        Chunks {
            chunk_size,
            slice: self.as_parallel_slice(),
        }
    }

    /// Parallel iterator over exact non-overlapping chunks of
    /// `chunk_size` items (the remainder is available via
    /// [`ChunksExact::remainder`] before driving).
    fn par_chunks_exact(&self, chunk_size: usize) -> ChunksExact<'_, T> {
        assert!(chunk_size != 0, "chunk_size must not be zero");
        let slice = self.as_parallel_slice();
        let rem_len = slice.len() % chunk_size;
        let len = slice.len() - rem_len;
        let (fst, snd) = slice.split_at(len);
        ChunksExact {
            chunk_size,
            slice: fst,
            rem: snd,
        }
    }

    /// Parallel iterator over all contiguous windows of length
    /// `window_size`, in overlapping fashion.
    fn par_windows(&self, window_size: usize) -> Windows<'_, T> {
        assert!(window_size != 0, "window_size must not be zero");
        Windows {
            window_size,
            slice: self.as_parallel_slice(),
        }
    }
}

impl<T: Sync> ParallelSlice<T> for [T] {
    #[inline]
    fn as_parallel_slice(&self) -> &[T] {
        self
    }
}

/// Parallel extensions for mutable slices.
pub trait ParallelSliceMut<T: Send> {
    /// Returns the slice (implementation detail).
    fn as_parallel_slice_mut(&mut self) -> &mut [T];

    /// Parallel iterator over mutable non-overlapping chunks.
    fn par_chunks_mut(&mut self, chunk_size: usize) -> ChunksMut<'_, T> {
        assert!(chunk_size != 0, "chunk_size must not be zero");
        ChunksMut {
            chunk_size,
            slice: self.as_parallel_slice_mut(),
        }
    }

    /// Sorts the slice in parallel, stably. Parallel merge sort with
    /// parallel merges; allocates one scratch buffer of the slice's
    /// size.
    fn par_sort(&mut self)
    where
        T: Ord,
    {
        crate::sort::par_mergesort(self.as_parallel_slice_mut(), T::cmp);
    }

    /// Stable parallel sort with a comparator.
    fn par_sort_by<F>(&mut self, compare: F)
    where
        F: Fn(&T, &T) -> std::cmp::Ordering + Sync,
    {
        crate::sort::par_mergesort(self.as_parallel_slice_mut(), compare);
    }

    /// Stable parallel sort by key.
    fn par_sort_by_key<K, F>(&mut self, f: F)
    where
        K: Ord,
        F: Fn(&T) -> K + Sync,
    {
        crate::sort::par_mergesort(self.as_parallel_slice_mut(), |a, b| f(a).cmp(&f(b)));
    }

    /// Sorts the slice in parallel, but not stably (equal elements may
    /// be reordered). Parallel three-way quicksort with std's pdqsort
    /// at the leaves.
    fn par_sort_unstable(&mut self)
    where
        T: Ord,
    {
        crate::sort::par_quicksort(self.as_parallel_slice_mut(), T::cmp);
    }

    /// Unstable parallel sort with a comparator.
    fn par_sort_unstable_by<F>(&mut self, compare: F)
    where
        F: Fn(&T, &T) -> std::cmp::Ordering + Sync,
    {
        crate::sort::par_quicksort(self.as_parallel_slice_mut(), compare);
    }

    /// Unstable parallel sort by key.
    fn par_sort_unstable_by_key<K, F>(&mut self, f: F)
    where
        K: Ord,
        F: Fn(&T) -> K + Sync,
    {
        crate::sort::par_quicksort(self.as_parallel_slice_mut(), |a, b| f(a).cmp(&f(b)));
    }
}

impl<T: Send> ParallelSliceMut<T> for [T] {
    #[inline]
    fn as_parallel_slice_mut(&mut self) -> &mut [T] {
        self
    }
}

// //////////////////////////////////////////////////////////////////////
// &[T]

/// Parallel iterator over `&[T]`.
#[derive(Debug, Clone)]
pub struct Iter<'data, T: Sync> {
    slice: &'data [T],
}

impl<'data, T: Sync + 'data> IntoParallelIterator for &'data [T] {
    type Iter = Iter<'data, T>;
    type Item = &'data T;

    fn into_par_iter(self) -> Self::Iter {
        Iter { slice: self }
    }
}

impl<'data, T: Sync + 'data> IntoParallelIterator for &'data Vec<T> {
    type Iter = Iter<'data, T>;
    type Item = &'data T;

    fn into_par_iter(self) -> Self::Iter {
        Iter { slice: self }
    }
}

impl<'data, T: Sync + 'data> ParallelIterator for Iter<'data, T> {
    type Item = &'data T;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn opt_len(&self) -> Option<usize> {
        Some(self.slice.len())
    }
}

impl<'data, T: Sync + 'data> IndexedParallelIterator for Iter<'data, T> {
    fn len(&self) -> usize {
        self.slice.len()
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
        callback.callback(IterProducer { slice: self.slice })
    }
}

struct IterProducer<'data, T: Sync> {
    slice: &'data [T],
}

impl<'data, T: 'data + Sync> Producer for IterProducer<'data, T> {
    type Item = &'data T;
    type IntoIter = std::slice::Iter<'data, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.slice.iter()
    }

    #[inline]
    fn split_at(self, index: usize) -> (Self, Self) {
        let (left, right) = self.slice.split_at(index);
        (IterProducer { slice: left }, IterProducer { slice: right })
    }
}

// //////////////////////////////////////////////////////////////////////
// &mut [T]

/// Parallel iterator over `&mut [T]`.
#[derive(Debug)]
pub struct IterMut<'data, T: Send> {
    slice: &'data mut [T],
}

impl<'data, T: Send + 'data> IntoParallelIterator for &'data mut [T] {
    type Iter = IterMut<'data, T>;
    type Item = &'data mut T;

    fn into_par_iter(self) -> Self::Iter {
        IterMut { slice: self }
    }
}

impl<'data, T: Send + 'data> IntoParallelIterator for &'data mut Vec<T> {
    type Iter = IterMut<'data, T>;
    type Item = &'data mut T;

    fn into_par_iter(self) -> Self::Iter {
        IterMut { slice: self }
    }
}

impl<'data, T: Send + 'data> ParallelIterator for IterMut<'data, T> {
    type Item = &'data mut T;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn opt_len(&self) -> Option<usize> {
        Some(self.slice.len())
    }
}

impl<'data, T: Send + 'data> IndexedParallelIterator for IterMut<'data, T> {
    fn len(&self) -> usize {
        self.slice.len()
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
        callback.callback(IterMutProducer { slice: self.slice })
    }
}

struct IterMutProducer<'data, T: Send> {
    slice: &'data mut [T],
}

impl<'data, T: 'data + Send> Producer for IterMutProducer<'data, T> {
    type Item = &'data mut T;
    type IntoIter = std::slice::IterMut<'data, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.slice.iter_mut()
    }

    #[inline]
    fn split_at(self, index: usize) -> (Self, Self) {
        let (left, right) = self.slice.split_at_mut(index);
        (
            IterMutProducer { slice: left },
            IterMutProducer { slice: right },
        )
    }
}

// //////////////////////////////////////////////////////////////////////
// Chunks

/// Parallel iterator over non-overlapping chunks of a slice.
#[derive(Debug, Clone)]
pub struct Chunks<'data, T: Sync> {
    chunk_size: usize,
    slice: &'data [T],
}

impl<'data, T: Sync + 'data> ParallelIterator for Chunks<'data, T> {
    type Item = &'data [T];

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

impl<'data, T: Sync + 'data> IndexedParallelIterator for Chunks<'data, T> {
    fn len(&self) -> usize {
        self.slice.len().div_ceil(self.chunk_size)
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
        callback.callback(ChunksProducer {
            chunk_size: self.chunk_size,
            slice: self.slice,
        })
    }
}

struct ChunksProducer<'data, T: Sync> {
    chunk_size: usize,
    slice: &'data [T],
}

impl<'data, T: 'data + Sync> Producer for ChunksProducer<'data, T> {
    type Item = &'data [T];
    type IntoIter = std::slice::Chunks<'data, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.slice.chunks(self.chunk_size)
    }

    fn split_at(self, index: usize) -> (Self, Self) {
        let elem_index = Ord::min(index * self.chunk_size, self.slice.len());
        let (left, right) = self.slice.split_at(elem_index);
        (
            ChunksProducer {
                chunk_size: self.chunk_size,
                slice: left,
            },
            ChunksProducer {
                chunk_size: self.chunk_size,
                slice: right,
            },
        )
    }
}

/// Parallel iterator over exact-size chunks of a slice.
#[derive(Debug, Clone)]
pub struct ChunksExact<'data, T: Sync> {
    chunk_size: usize,
    slice: &'data [T],
    rem: &'data [T],
}

impl<'data, T: Sync> ChunksExact<'data, T> {
    /// The remainder of the original slice that will not be included.
    pub fn remainder(&self) -> &'data [T] {
        self.rem
    }
}

impl<'data, T: Sync + 'data> ParallelIterator for ChunksExact<'data, T> {
    type Item = &'data [T];

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

impl<'data, T: Sync + 'data> IndexedParallelIterator for ChunksExact<'data, T> {
    fn len(&self) -> usize {
        self.slice.len() / self.chunk_size
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
        callback.callback(ChunksExactProducer {
            chunk_size: self.chunk_size,
            slice: self.slice,
        })
    }
}

struct ChunksExactProducer<'data, T: Sync> {
    chunk_size: usize,
    slice: &'data [T],
}

impl<'data, T: 'data + Sync> Producer for ChunksExactProducer<'data, T> {
    type Item = &'data [T];
    type IntoIter = std::slice::ChunksExact<'data, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.slice.chunks_exact(self.chunk_size)
    }

    fn split_at(self, index: usize) -> (Self, Self) {
        let elem_index = index * self.chunk_size;
        let (left, right) = self.slice.split_at(elem_index);
        (
            ChunksExactProducer {
                chunk_size: self.chunk_size,
                slice: left,
            },
            ChunksExactProducer {
                chunk_size: self.chunk_size,
                slice: right,
            },
        )
    }
}

/// Parallel iterator over overlapping windows of a slice.
#[derive(Debug, Clone)]
pub struct Windows<'data, T: Sync> {
    window_size: usize,
    slice: &'data [T],
}

impl<'data, T: Sync + 'data> ParallelIterator for Windows<'data, T> {
    type Item = &'data [T];

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

impl<'data, T: Sync + 'data> IndexedParallelIterator for Windows<'data, T> {
    fn len(&self) -> usize {
        self.slice.len().saturating_sub(self.window_size - 1)
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
        callback.callback(WindowsProducer {
            window_size: self.window_size,
            slice: self.slice,
        })
    }
}

struct WindowsProducer<'data, T: Sync> {
    window_size: usize,
    slice: &'data [T],
}

impl<'data, T: 'data + Sync> Producer for WindowsProducer<'data, T> {
    type Item = &'data [T];
    type IntoIter = std::slice::Windows<'data, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.slice.windows(self.window_size)
    }

    fn split_at(self, index: usize) -> (Self, Self) {
        let left = &self.slice[..Ord::min(index + self.window_size - 1, self.slice.len())];
        let right = &self.slice[index..];
        (
            WindowsProducer {
                window_size: self.window_size,
                slice: left,
            },
            WindowsProducer {
                window_size: self.window_size,
                slice: right,
            },
        )
    }
}

/// Parallel iterator over mutable non-overlapping chunks of a slice.
#[derive(Debug)]
pub struct ChunksMut<'data, T: Send> {
    chunk_size: usize,
    slice: &'data mut [T],
}

impl<'data, T: Send + 'data> ParallelIterator for ChunksMut<'data, T> {
    type Item = &'data mut [T];

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

impl<'data, T: Send + 'data> IndexedParallelIterator for ChunksMut<'data, T> {
    fn len(&self) -> usize {
        self.slice.len().div_ceil(self.chunk_size)
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
        callback.callback(ChunksMutProducer {
            chunk_size: self.chunk_size,
            slice: self.slice,
        })
    }
}

struct ChunksMutProducer<'data, T: Send> {
    chunk_size: usize,
    slice: &'data mut [T],
}

impl<'data, T: 'data + Send> Producer for ChunksMutProducer<'data, T> {
    type Item = &'data mut [T];
    type IntoIter = std::slice::ChunksMut<'data, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.slice.chunks_mut(self.chunk_size)
    }

    fn split_at(self, index: usize) -> (Self, Self) {
        let elem_index = Ord::min(index * self.chunk_size, self.slice.len());
        let (left, right) = self.slice.split_at_mut(elem_index);
        (
            ChunksMutProducer {
                chunk_size: self.chunk_size,
                slice: left,
            },
            ChunksMutProducer {
                chunk_size: self.chunk_size,
                slice: right,
            },
        )
    }
}
