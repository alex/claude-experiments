//! `flat_map` / `flatten` (parallel inner iterators) and
//! `flat_map_iter` / `flatten_iter` (sequential inner iterators).
//!
//! Use the `_iter` forms when the inner collections are small: they
//! avoid per-item parallel-driver overhead and keep leaves sequential.

use super::plumbing::{Consumer, Folder, UnindexedConsumer};
use super::{IntoParallelIterator, ParallelIterator};

/// Created by [`ParallelIterator::flat_map`].
#[derive(Debug, Clone)]
pub struct FlatMap<I, F> {
    base: I,
    map_op: F,
}

impl<I, F> FlatMap<I, F> {
    pub(super) fn new(base: I, map_op: F) -> Self {
        FlatMap { base, map_op }
    }
}

impl<I, F, PI> ParallelIterator for FlatMap<I, F>
where
    I: ParallelIterator,
    F: Fn(I::Item) -> PI + Sync + Send,
    PI: IntoParallelIterator,
{
    type Item = PI::Item;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        let consumer = FlatMapConsumer {
            base: consumer,
            map_op: &self.map_op,
        };
        self.base.drive_unindexed(consumer)
    }
}

struct FlatMapConsumer<'f, C, F> {
    base: C,
    map_op: &'f F,
}

impl<'f, T, U, C, F> Consumer<T> for FlatMapConsumer<'f, C, F>
where
    C: UnindexedConsumer<U::Item>,
    F: Fn(T) -> U + Sync,
    U: IntoParallelIterator,
{
    type Folder = FlatMapFolder<'f, C, F, C::Result>;
    type Reducer = C::Reducer;
    type Result = C::Result;

    fn split_at(self, _index: usize) -> (Self, Self, Self::Reducer) {
        (
            FlatMapConsumer {
                base: self.base.split_off_left(),
                map_op: self.map_op,
            },
            FlatMapConsumer {
                base: self.base.split_off_left(),
                map_op: self.map_op,
            },
            self.base.to_reducer(),
        )
    }

    fn into_folder(self) -> Self::Folder {
        FlatMapFolder {
            base: self.base,
            map_op: self.map_op,
            previous: None,
        }
    }

    fn full(&self) -> bool {
        self.base.full()
    }
}

impl<'f, T, U, C, F> UnindexedConsumer<T> for FlatMapConsumer<'f, C, F>
where
    C: UnindexedConsumer<U::Item>,
    F: Fn(T) -> U + Sync,
    U: IntoParallelIterator,
{
    fn split_off_left(&self) -> Self {
        FlatMapConsumer {
            base: self.base.split_off_left(),
            map_op: self.map_op,
        }
    }

    fn to_reducer(&self) -> Self::Reducer {
        self.base.to_reducer()
    }
}

struct FlatMapFolder<'f, C, F, R> {
    base: C,
    map_op: &'f F,
    previous: Option<R>,
}

impl<'f, T, U, C, F> Folder<T> for FlatMapFolder<'f, C, F, C::Result>
where
    C: UnindexedConsumer<U::Item>,
    F: Fn(T) -> U + Sync,
    U: IntoParallelIterator,
{
    type Result = C::Result;

    fn consume(self, item: T) -> Self {
        let map_op = self.map_op;
        let par_iter = map_op(item).into_par_iter();
        let consumer = self.base.split_off_left();
        let result = par_iter.drive_unindexed(consumer);

        let previous = match self.previous {
            None => Some(result),
            Some(previous) => {
                let reducer = self.base.to_reducer();
                Some(reducer.reduce(previous, result))
            }
        };

        FlatMapFolder {
            base: self.base,
            map_op,
            previous,
        }
    }

    fn complete(self) -> Self::Result {
        match self.previous {
            Some(previous) => previous,
            None => self.base.into_folder().complete(),
        }
    }

    fn full(&self) -> bool {
        self.base.full()
    }
}

use super::plumbing::Reducer as _;

/// Created by [`ParallelIterator::flat_map_iter`].
#[derive(Debug, Clone)]
pub struct FlatMapIter<I, F> {
    base: I,
    map_op: F,
}

impl<I, F> FlatMapIter<I, F> {
    pub(super) fn new(base: I, map_op: F) -> Self {
        FlatMapIter { base, map_op }
    }
}

impl<I, F, SI> ParallelIterator for FlatMapIter<I, F>
where
    I: ParallelIterator,
    F: Fn(I::Item) -> SI + Sync + Send,
    SI: IntoIterator,
    SI::Item: Send,
{
    type Item = SI::Item;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        let consumer = FlatMapIterConsumer {
            base: consumer,
            map_op: &self.map_op,
        };
        self.base.drive_unindexed(consumer)
    }
}

struct FlatMapIterConsumer<'f, C, F> {
    base: C,
    map_op: &'f F,
}

impl<'f, T, U, C, F> Consumer<T> for FlatMapIterConsumer<'f, C, F>
where
    C: Consumer<U::Item>,
    F: Fn(T) -> U + Sync,
    U: IntoIterator,
{
    type Folder = FlatMapIterFolder<'f, C::Folder, F>;
    type Reducer = C::Reducer;
    type Result = C::Result;

    fn split_at(self, index: usize) -> (Self, Self, Self::Reducer) {
        let (left, right, reducer) = self.base.split_at(index);
        (
            FlatMapIterConsumer {
                base: left,
                map_op: self.map_op,
            },
            FlatMapIterConsumer {
                base: right,
                map_op: self.map_op,
            },
            reducer,
        )
    }

    fn into_folder(self) -> Self::Folder {
        FlatMapIterFolder {
            base: self.base.into_folder(),
            map_op: self.map_op,
        }
    }

    fn full(&self) -> bool {
        self.base.full()
    }
}

impl<'f, T, U, C, F> UnindexedConsumer<T> for FlatMapIterConsumer<'f, C, F>
where
    C: UnindexedConsumer<U::Item>,
    F: Fn(T) -> U + Sync,
    U: IntoIterator,
{
    fn split_off_left(&self) -> Self {
        FlatMapIterConsumer {
            base: self.base.split_off_left(),
            map_op: self.map_op,
        }
    }

    fn to_reducer(&self) -> Self::Reducer {
        self.base.to_reducer()
    }
}

struct FlatMapIterFolder<'f, C, F> {
    base: C,
    map_op: &'f F,
}

impl<'f, T, U, C, F> Folder<T> for FlatMapIterFolder<'f, C, F>
where
    C: Folder<U::Item>,
    F: Fn(T) -> U,
    U: IntoIterator,
{
    type Result = C::Result;

    #[inline]
    fn consume(self, item: T) -> Self {
        let map_op = self.map_op;
        let base = self.base.consume_iter(map_op(item));
        FlatMapIterFolder { base, map_op }
    }

    #[inline]
    fn consume_iter<I>(self, iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let map_op = self.map_op;
        let iter = iter.into_iter().flat_map(map_op);
        let base = self.base.consume_iter(iter);
        FlatMapIterFolder { base, map_op }
    }

    fn complete(self) -> Self::Result {
        self.base.complete()
    }

    fn full(&self) -> bool {
        self.base.full()
    }
}

/// Created by [`ParallelIterator::flatten`].
#[derive(Debug, Clone)]
pub struct Flatten<I> {
    base: I,
}

impl<I> Flatten<I> {
    pub(super) fn new(base: I) -> Self {
        Flatten { base }
    }
}

impl<I, PI> ParallelIterator for Flatten<I>
where
    I: ParallelIterator<Item = PI>,
    PI: IntoParallelIterator + Send,
{
    type Item = PI::Item;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        let consumer = FlatMapConsumer {
            base: consumer,
            map_op: &|x: PI| x,
        };
        self.base.drive_unindexed(consumer)
    }
}

/// Created by [`ParallelIterator::flatten_iter`].
#[derive(Debug, Clone)]
pub struct FlattenIter<I> {
    base: I,
}

impl<I> FlattenIter<I> {
    pub(super) fn new(base: I) -> Self {
        FlattenIter { base }
    }
}

impl<I, SI> ParallelIterator for FlattenIter<I>
where
    I: ParallelIterator<Item = SI>,
    SI: IntoIterator + Send,
    SI::Item: Send,
{
    type Item = SI::Item;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        let consumer = FlatMapIterConsumer {
            base: consumer,
            map_op: &|x: SI| x,
        };
        self.base.drive_unindexed(consumer)
    }
}
