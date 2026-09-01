//! `skip(n)` and `take(n)` for indexed iterators: implemented by
//! splitting the producer once and keeping the relevant side, so they
//! add zero per-item overhead.

use super::plumbing::{bridge, Consumer, Producer, ProducerCallback, UnindexedConsumer};
use super::{IndexedParallelIterator, ParallelIterator};

/// Created by [`IndexedParallelIterator::take`].
#[derive(Debug, Clone)]
pub struct Take<I> {
    base: I,
    n: usize,
}

impl<I: IndexedParallelIterator> Take<I> {
    pub(super) fn new(base: I, n: usize) -> Self {
        let n = Ord::min(base.len(), n);
        Take { base, n }
    }
}

impl<I> ParallelIterator for Take<I>
where
    I: IndexedParallelIterator,
{
    type Item = I::Item;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn opt_len(&self) -> Option<usize> {
        Some(self.n)
    }
}

impl<I> IndexedParallelIterator for Take<I>
where
    I: IndexedParallelIterator,
{
    fn drive<C>(self, consumer: C) -> C::Result
    where
        C: Consumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn len(&self) -> usize {
        self.n
    }

    fn with_producer<CB>(self, callback: CB) -> CB::Output
    where
        CB: ProducerCallback<Self::Item>,
    {
        return self.base.with_producer(Callback {
            callback,
            n: self.n,
        });

        struct Callback<CB> {
            callback: CB,
            n: usize,
        }

        impl<T, CB> ProducerCallback<T> for Callback<CB>
        where
            CB: ProducerCallback<T>,
        {
            type Output = CB::Output;

            fn callback<P>(self, base: P) -> CB::Output
            where
                P: Producer<Item = T>,
            {
                let (producer, _) = base.split_at(self.n);
                self.callback.callback(producer)
            }
        }
    }
}

/// Created by [`IndexedParallelIterator::skip`].
#[derive(Debug, Clone)]
pub struct Skip<I> {
    base: I,
    n: usize,
}

impl<I: IndexedParallelIterator> Skip<I> {
    pub(super) fn new(base: I, n: usize) -> Self {
        let n = Ord::min(base.len(), n);
        Skip { base, n }
    }
}

impl<I> ParallelIterator for Skip<I>
where
    I: IndexedParallelIterator,
{
    type Item = I::Item;

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

impl<I> IndexedParallelIterator for Skip<I>
where
    I: IndexedParallelIterator,
{
    fn drive<C>(self, consumer: C) -> C::Result
    where
        C: Consumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn len(&self) -> usize {
        self.base.len() - self.n
    }

    fn with_producer<CB>(self, callback: CB) -> CB::Output
    where
        CB: ProducerCallback<Self::Item>,
    {
        return self.base.with_producer(Callback {
            callback,
            n: self.n,
        });

        struct Callback<CB> {
            callback: CB,
            n: usize,
        }

        impl<T, CB> ProducerCallback<T> for Callback<CB>
        where
            CB: ProducerCallback<T>,
        {
            type Output = CB::Output;

            fn callback<P>(self, base: P) -> CB::Output
            where
                P: Producer<Item = T>,
            {
                let (_, producer) = base.split_at(self.n);
                self.callback.callback(producer)
            }
        }
    }
}
