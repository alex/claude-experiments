use super::plumbing::{bridge, Consumer, Producer, ProducerCallback, UnindexedConsumer};
use super::{IndexedParallelIterator, ParallelIterator};
use std::iter;
use std::ops::Range;

/// `Enumerate` yields `(index, item)` pairs. Created by
/// [`IndexedParallelIterator::enumerate`].
#[derive(Debug, Clone)]
pub struct Enumerate<I> {
    base: I,
}

impl<I> Enumerate<I> {
    pub(super) fn new(base: I) -> Self {
        Enumerate { base }
    }
}

impl<I> ParallelIterator for Enumerate<I>
where
    I: IndexedParallelIterator,
{
    type Item = (usize, I::Item);

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn opt_len(&self) -> Option<usize> {
        Some(self.base.len())
    }
}

impl<I> IndexedParallelIterator for Enumerate<I>
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
        self.base.len()
    }

    fn with_producer<CB>(self, callback: CB) -> CB::Output
    where
        CB: ProducerCallback<Self::Item>,
    {
        return self.base.with_producer(Callback { callback });

        struct Callback<CB> {
            callback: CB,
        }

        impl<I, CB> ProducerCallback<I> for Callback<CB>
        where
            CB: ProducerCallback<(usize, I)>,
        {
            type Output = CB::Output;

            fn callback<P>(self, base: P) -> CB::Output
            where
                P: Producer<Item = I>,
            {
                self.callback.callback(EnumerateProducer { base, offset: 0 })
            }
        }
    }
}

struct EnumerateProducer<P> {
    base: P,
    offset: usize,
}

impl<P> Producer for EnumerateProducer<P>
where
    P: Producer,
{
    type Item = (usize, P::Item);
    type IntoIter = iter::Zip<Range<usize>, P::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        let base = self.base.into_iter();
        let end = self.offset + base.len();
        (self.offset..end).zip(base)
    }

    fn min_len(&self) -> usize {
        self.base.min_len()
    }

    fn max_len(&self) -> usize {
        self.base.max_len()
    }

    fn split_at(self, index: usize) -> (Self, Self) {
        let (left, right) = self.base.split_at(index);
        (
            EnumerateProducer {
                base: left,
                offset: self.offset,
            },
            EnumerateProducer {
                base: right,
                offset: self.offset + index,
            },
        )
    }
}
