//! Parallel iterator traits and adapters.
//!
//! This module mirrors the structure of `std::iter` (and of rayon): the
//! main traits are [`ParallelIterator`] (any parallel sequence) and
//! [`IndexedParallelIterator`] (known length + stable indices), with
//! conversion traits [`IntoParallelIterator`], [`IntoParallelRefIterator`]
//! and [`IntoParallelRefMutIterator`] to obtain them from collections.

pub mod plumbing;

mod collect;
mod count;
mod for_each;
mod map;
mod noop;
mod reduce;
mod sum;

pub use self::collect::collect_into_vec;
pub use self::map::Map;

use self::plumbing::{Consumer, ProducerCallback, UnindexedConsumer};
use std::iter::Sum;

/// Converts into a parallel iterator, consuming `self`.
///
/// Implemented for collections (by value, yielding owned items) and for
/// references to collections (yielding references). Parallel iterators
/// themselves also implement it (identity), so adapter methods accept
/// `impl IntoParallelIterator` arguments.
pub trait IntoParallelIterator {
    type Iter: ParallelIterator<Item = Self::Item>;
    type Item: Send;

    fn into_par_iter(self) -> Self::Iter;
}

impl<T: ParallelIterator> IntoParallelIterator for T {
    type Iter = T;
    type Item = T::Item;

    fn into_par_iter(self) -> Self {
        self
    }
}

/// `collection.par_iter()`: parallel iterator over shared references.
///
/// Blanket-implemented for any `I` where `&I: IntoParallelIterator`.
pub trait IntoParallelRefIterator<'data> {
    type Iter: ParallelIterator<Item = Self::Item>;
    type Item: Send + 'data;

    fn par_iter(&'data self) -> Self::Iter;
}

impl<'data, I: 'data + ?Sized> IntoParallelRefIterator<'data> for I
where
    &'data I: IntoParallelIterator,
{
    type Iter = <&'data I as IntoParallelIterator>::Iter;
    type Item = <&'data I as IntoParallelIterator>::Item;

    fn par_iter(&'data self) -> Self::Iter {
        self.into_par_iter()
    }
}

/// `collection.par_iter_mut()`: parallel iterator over mutable references.
pub trait IntoParallelRefMutIterator<'data> {
    type Iter: ParallelIterator<Item = Self::Item>;
    type Item: Send + 'data;

    fn par_iter_mut(&'data mut self) -> Self::Iter;
}

impl<'data, I: 'data + ?Sized> IntoParallelRefMutIterator<'data> for I
where
    &'data mut I: IntoParallelIterator,
{
    type Iter = <&'data mut I as IntoParallelIterator>::Iter;
    type Item = <&'data mut I as IntoParallelIterator>::Item;

    fn par_iter_mut(&'data mut self) -> Self::Iter {
        self.into_par_iter()
    }
}

/// Collect items from a parallel iterator into a collection.
pub trait FromParallelIterator<T>
where
    T: Send,
{
    fn from_par_iter<I>(par_iter: I) -> Self
    where
        I: IntoParallelIterator<Item = T>;
}

/// Extend a collection with items from a parallel iterator.
pub trait ParallelExtend<T>
where
    T: Send,
{
    fn par_extend<I>(&mut self, par_iter: I)
    where
        I: IntoParallelIterator<Item = T>;
}

/// An iterator that can be executed in parallel.
///
/// All adapter methods have the same semantics as their sequential
/// counterparts on [`Iterator`], except that execution order is
/// unspecified.
pub trait ParallelIterator: Sized + Send {
    type Item: Send;

    /// Internal: drives this iterator into the given consumer. This is
    /// the method implementors write; users call the adapter methods.
    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>;

    /// Internal: exact length, if cheaply known. Enables optimized exact
    /// collection.
    fn opt_len(&self) -> Option<usize> {
        None
    }

    /// Executes `op` on every item, in parallel.
    fn for_each<OP>(self, op: OP)
    where
        OP: Fn(Self::Item) + Sync + Send,
    {
        for_each::for_each(self, &op)
    }

    /// Maps each item to a new value.
    fn map<F, R>(self, map_op: F) -> Map<Self, F>
    where
        F: Fn(Self::Item) -> R + Sync + Send,
        R: Send,
    {
        Map::new(self, map_op)
    }

    /// Sums the items (or anything `Sum`-compatible).
    fn sum<S>(self) -> S
    where
        S: Send + Sum<Self::Item> + Sum<S>,
    {
        sum::sum(self)
    }

    /// Reduces the items to a single one using `op`, with `identity` as
    /// the neutral element supplier.
    fn reduce<OP, ID>(self, identity: ID, op: OP) -> Self::Item
    where
        OP: Fn(Self::Item, Self::Item) -> Self::Item + Sync + Send,
        ID: Fn() -> Self::Item + Sync + Send,
    {
        reduce::reduce(self, identity, op)
    }

    /// Counts the items.
    fn count(self) -> usize {
        count::count(self)
    }

    /// Collects into any [`FromParallelIterator`] collection.
    fn collect<C>(self) -> C
    where
        C: FromParallelIterator<Self::Item>,
    {
        C::from_par_iter(self)
    }
}

/// A parallel iterator with known exact length and stable item indices,
/// supporting index-dependent adapters (`zip`, `enumerate`, ...) and
/// in-place collection.
pub trait IndexedParallelIterator: ParallelIterator {
    /// The exact number of items.
    #[allow(clippy::len_without_is_empty)]
    fn len(&self) -> usize;

    /// Internal: drives this iterator into an (indexed) consumer.
    fn drive<C: Consumer<Self::Item>>(self, consumer: C) -> C::Result;

    /// Internal: converts to a [`plumbing::Producer`], handed to the
    /// callback (continuation style, since the producer type is private).
    fn with_producer<CB: ProducerCallback<Self::Item>>(self, callback: CB) -> CB::Output;

    /// Collects into `target`, replacing its contents; the vector's
    /// allocation is reused and items are written in place, in parallel.
    fn collect_into_vec(self, target: &mut Vec<Self::Item>) {
        collect::collect_into_vec(self, target);
    }
}
