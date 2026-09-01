//! `copied()` and `cloned()`: adapters converting `&T` items to `T`.
//! Both are fully indexed (producer + consumer forms) and compose the
//! std `copied`/`cloned` adapters at the leaves.

use super::plumbing::{Consumer, Folder, Producer, ProducerCallback, UnindexedConsumer};
use super::{IndexedParallelIterator, ParallelIterator};
use std::iter;

macro_rules! copy_clone_adapter {
    ($name:ident, $producer:ident, $consumer:ident, $folder:ident, $bound:ident,
     $std_adapter:ident, $consume:expr) => {
        /// Adapter converting `&T` items to owned `T` values.
        #[derive(Debug, Clone)]
        pub struct $name<I> {
            base: I,
        }

        impl<I> $name<I> {
            pub(super) fn new(base: I) -> Self {
                $name { base }
            }
        }

        impl<'a, T, I> ParallelIterator for $name<I>
        where
            I: ParallelIterator<Item = &'a T>,
            T: 'a + $bound + Send + Sync,
        {
            type Item = T;

            fn drive_unindexed<C>(self, consumer: C) -> C::Result
            where
                C: UnindexedConsumer<Self::Item>,
            {
                self.base.drive_unindexed($consumer { base: consumer })
            }

            fn opt_len(&self) -> Option<usize> {
                self.base.opt_len()
            }
        }

        impl<'a, T, I> IndexedParallelIterator for $name<I>
        where
            I: IndexedParallelIterator<Item = &'a T>,
            T: 'a + $bound + Send + Sync,
        {
            fn drive<C>(self, consumer: C) -> C::Result
            where
                C: Consumer<Self::Item>,
            {
                self.base.drive($consumer { base: consumer })
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

                impl<'a, T, CB> ProducerCallback<&'a T> for Callback<CB>
                where
                    CB: ProducerCallback<T>,
                    T: 'a + $bound + Send + Sync,
                {
                    type Output = CB::Output;

                    fn callback<P>(self, base: P) -> CB::Output
                    where
                        P: Producer<Item = &'a T>,
                    {
                        self.callback.callback($producer { base })
                    }
                }
            }
        }

        struct $producer<P> {
            base: P,
        }

        impl<'a, T, P> Producer for $producer<P>
        where
            P: Producer<Item = &'a T>,
            T: 'a + $bound + Send + Sync,
        {
            type Item = T;
            type IntoIter = iter::$name<P::IntoIter>;

            fn into_iter(self) -> Self::IntoIter {
                self.base.into_iter().$std_adapter()
            }

            fn min_len(&self) -> usize {
                self.base.min_len()
            }

            fn max_len(&self) -> usize {
                self.base.max_len()
            }

            fn split_at(self, index: usize) -> (Self, Self) {
                let (left, right) = self.base.split_at(index);
                ($producer { base: left }, $producer { base: right })
            }

            fn fold_with<F>(self, folder: F) -> F
            where
                F: Folder<Self::Item>,
            {
                self.base.fold_with($folder { base: folder }).base
            }
        }

        struct $consumer<C> {
            base: C,
        }

        impl<'a, T, C> Consumer<&'a T> for $consumer<C>
        where
            C: Consumer<T>,
            T: 'a + $bound + Send + Sync,
        {
            type Folder = $folder<C::Folder>;
            type Reducer = C::Reducer;
            type Result = C::Result;

            fn split_at(self, index: usize) -> (Self, Self, Self::Reducer) {
                let (left, right, reducer) = self.base.split_at(index);
                (
                    $consumer { base: left },
                    $consumer { base: right },
                    reducer,
                )
            }

            fn into_folder(self) -> Self::Folder {
                $folder {
                    base: self.base.into_folder(),
                }
            }

            fn full(&self) -> bool {
                self.base.full()
            }
        }

        impl<'a, T, C> UnindexedConsumer<&'a T> for $consumer<C>
        where
            C: UnindexedConsumer<T>,
            T: 'a + $bound + Send + Sync,
        {
            fn split_off_left(&self) -> Self {
                $consumer {
                    base: self.base.split_off_left(),
                }
            }

            fn to_reducer(&self) -> Self::Reducer {
                self.base.to_reducer()
            }
        }

        struct $folder<C> {
            base: C,
        }

        impl<'a, T, C> Folder<&'a T> for $folder<C>
        where
            C: Folder<T>,
            T: 'a + $bound,
        {
            type Result = C::Result;

            #[inline]
            fn consume(self, item: &'a T) -> Self {
                $folder {
                    base: self.base.consume($consume(item)),
                }
            }

            #[inline]
            fn consume_iter<I>(mut self, iter: I) -> Self
            where
                I: IntoIterator<Item = &'a T>,
            {
                self.base = self.base.consume_iter(iter.into_iter().$std_adapter());
                self
            }

            fn complete(self) -> C::Result {
                self.base.complete()
            }

            fn full(&self) -> bool {
                self.base.full()
            }
        }
    };
}

copy_clone_adapter!(
    Copied,
    CopiedProducer,
    CopiedConsumer,
    CopiedFolder,
    Copy,
    copied,
    |item: &T| *item
);
copy_clone_adapter!(
    Cloned,
    ClonedProducer,
    ClonedConsumer,
    ClonedFolder,
    Clone,
    cloned,
    |item: &T| item.clone()
);
