//! `with_min_len` / `with_max_len`: granularity control for the
//! adaptive splitter.

use super::plumbing::{bridge, Consumer, Folder, Producer, ProducerCallback, UnindexedConsumer};
use super::{IndexedParallelIterator, ParallelIterator};

macro_rules! len_adapter_common {
    ($name:ident, $producer:ident, $field:ident) => {
        /// Granularity-control adapter (see
        /// [`IndexedParallelIterator::with_min_len`] /
        /// [`IndexedParallelIterator::with_max_len`]).
        #[derive(Debug, Clone)]
        pub struct $name<I> {
            base: I,
            $field: usize,
        }

        impl<I> $name<I> {
            pub(super) fn new(base: I, $field: usize) -> Self {
                $name { base, $field }
            }
        }

        impl<I> ParallelIterator for $name<I>
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

        impl<I> IndexedParallelIterator for $name<I>
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
                return self.base.with_producer(Callback {
                    callback,
                    $field: self.$field,
                });

                struct Callback<CB> {
                    callback: CB,
                    $field: usize,
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
                        self.callback.callback($producer {
                            base,
                            $field: self.$field,
                        })
                    }
                }
            }
        }

        struct $producer<P> {
            base: P,
            $field: usize,
        }
    };
}

len_adapter_common!(MinLen, MinLenProducer, min);

impl<P> Producer for MinLenProducer<P>
where
    P: Producer,
{
    type Item = P::Item;
    type IntoIter = P::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.base.into_iter()
    }

    fn min_len(&self) -> usize {
        Ord::max(self.min, self.base.min_len())
    }

    fn max_len(&self) -> usize {
        self.base.max_len()
    }

    fn split_at(self, index: usize) -> (Self, Self) {
        let (left, right) = self.base.split_at(index);
        (
            MinLenProducer {
                base: left,
                min: self.min,
            },
            MinLenProducer {
                base: right,
                min: self.min,
            },
        )
    }

    fn fold_with<F>(self, folder: F) -> F
    where
        F: Folder<Self::Item>,
    {
        self.base.fold_with(folder)
    }
}

len_adapter_common!(MaxLen, MaxLenProducer, max);

impl<P> Producer for MaxLenProducer<P>
where
    P: Producer,
{
    type Item = P::Item;
    type IntoIter = P::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.base.into_iter()
    }

    fn min_len(&self) -> usize {
        self.base.min_len()
    }

    fn max_len(&self) -> usize {
        Ord::min(self.max, self.base.max_len())
    }

    fn split_at(self, index: usize) -> (Self, Self) {
        let (left, right) = self.base.split_at(index);
        (
            MaxLenProducer {
                base: left,
                max: self.max,
            },
            MaxLenProducer {
                base: right,
                max: self.max,
            },
        )
    }

    fn fold_with<F>(self, folder: F) -> F
    where
        F: Folder<Self::Item>,
    {
        self.base.fold_with(folder)
    }
}
