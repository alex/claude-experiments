use super::plumbing::{bridge, Consumer, Producer, ProducerCallback, UnindexedConsumer};
use super::{IndexedParallelIterator, ParallelIterator};
use std::iter;

/// `Rev` yields items in the opposite order. Created by
/// [`IndexedParallelIterator::rev`].
#[derive(Debug, Clone)]
pub struct Rev<I> {
    base: I,
}

impl<I> Rev<I> {
    pub(super) fn new(base: I) -> Self {
        Rev { base }
    }
}

impl<I> ParallelIterator for Rev<I>
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
        Some(self.base.len())
    }
}

impl<I> IndexedParallelIterator for Rev<I>
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
        let len = self.base.len();
        return self.base.with_producer(Callback { callback, len });

        struct Callback<CB> {
            callback: CB,
            len: usize,
        }

        impl<I, CB> ProducerCallback<I> for Callback<CB>
        where
            CB: ProducerCallback<I>,
        {
            type Output = CB::Output;

            fn callback<P>(self, base: P) -> CB::Output
            where
                P: Producer<Item = I>,
            {
                self.callback.callback(RevProducer {
                    base,
                    len: self.len,
                })
            }
        }
    }
}

struct RevProducer<P> {
    base: P,
    len: usize,
}

impl<P> Producer for RevProducer<P>
where
    P: Producer,
{
    type Item = P::Item;
    type IntoIter = iter::Rev<P::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        self.base.into_iter().rev()
    }

    fn min_len(&self) -> usize {
        self.base.min_len()
    }

    fn max_len(&self) -> usize {
        self.base.max_len()
    }

    fn split_at(self, index: usize) -> (Self, Self) {
        let (left, right) = self.base.split_at(self.len - index);
        (
            RevProducer {
                base: right,
                len: index,
            },
            RevProducer {
                base: left,
                len: self.len - index,
            },
        )
    }
}
