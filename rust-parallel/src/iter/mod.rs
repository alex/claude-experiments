//! Parallel iterator traits and adapters.
//!
//! This module mirrors the structure of `std::iter` (and of rayon): the
//! main traits are [`ParallelIterator`] (any parallel sequence) and
//! [`IndexedParallelIterator`] (known length + stable indices), with
//! conversion traits [`IntoParallelIterator`], [`IntoParallelRefIterator`]
//! and [`IntoParallelRefMutIterator`] to obtain them from collections.

pub mod plumbing;

mod chain;
mod collect;
mod copy_clone;
mod count;
mod enumerate;
mod filter;
mod filter_map;
mod find;
mod flat_map;
mod fold;
mod for_each;
mod from_par_iter;
mod inspect;
mod len;
mod map;
mod noop;
mod product;
mod reduce;
mod rev;
mod skip_take;
mod sum;
mod zip;

pub use self::chain::Chain;
pub use self::collect::collect_into_vec;
pub use self::copy_clone::{Cloned, Copied};
pub use self::enumerate::Enumerate;
pub use self::filter::Filter;
pub use self::filter_map::FilterMap;
pub use self::flat_map::{FlatMap, FlatMapIter, Flatten, FlattenIter};
pub use self::fold::{Fold, FoldWith};
pub use self::inspect::Inspect;
pub use self::len::{MaxLen, MinLen};
pub use self::map::Map;
pub use self::rev::Rev;
pub use self::skip_take::{Skip, Take};
pub use self::zip::Zip;

use self::plumbing::{Consumer, ProducerCallback, UnindexedConsumer};
use std::cmp::Ordering;
use std::iter::{Product, Sum};

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

    /// Keeps only items matching `filter_op`.
    fn filter<P>(self, filter_op: P) -> Filter<Self, P>
    where
        P: Fn(&Self::Item) -> bool + Sync + Send,
    {
        Filter::new(self, filter_op)
    }

    /// Simultaneously filters and maps.
    fn filter_map<P, R>(self, filter_op: P) -> FilterMap<Self, P>
    where
        P: Fn(Self::Item) -> Option<R> + Sync + Send,
        R: Send,
    {
        FilterMap::new(self, filter_op)
    }

    /// Maps each item to a *parallel* iterator and flattens the results.
    /// Prefer [`flat_map_iter`](Self::flat_map_iter) when the inner
    /// collections are cheap to iterate sequentially.
    fn flat_map<F, PI>(self, map_op: F) -> FlatMap<Self, F>
    where
        F: Fn(Self::Item) -> PI + Sync + Send,
        PI: IntoParallelIterator,
    {
        FlatMap::new(self, map_op)
    }

    /// Maps each item to a *sequential* iterator and flattens the
    /// results.
    fn flat_map_iter<F, SI>(self, map_op: F) -> FlatMapIter<Self, F>
    where
        F: Fn(Self::Item) -> SI + Sync + Send,
        SI: IntoIterator,
        SI::Item: Send,
    {
        FlatMapIter::new(self, map_op)
    }

    /// Flattens nested parallel iterators.
    fn flatten(self) -> Flatten<Self>
    where
        Self::Item: IntoParallelIterator,
    {
        Flatten::new(self)
    }

    /// Flattens nested sequential iterators.
    fn flatten_iter(self) -> FlattenIter<Self>
    where
        Self::Item: IntoIterator,
        <Self::Item as IntoIterator>::Item: Send,
    {
        FlattenIter::new(self)
    }

    /// Calls `inspect_op` on a reference to each item.
    fn inspect<OP>(self, inspect_op: OP) -> Inspect<Self, OP>
    where
        OP: Fn(&Self::Item) + Sync + Send,
    {
        Inspect::new(self, inspect_op)
    }

    /// Copies `&T` items into `T` items.
    fn copied<'a, T>(self) -> Copied<Self>
    where
        T: 'a + Copy + Send + Sync,
        Self: ParallelIterator<Item = &'a T>,
    {
        Copied::new(self)
    }

    /// Clones `&T` items into `T` items.
    fn cloned<'a, T>(self) -> Cloned<Self>
    where
        T: 'a + Clone + Send + Sync,
        Self: ParallelIterator<Item = &'a T>,
    {
        Cloned::new(self)
    }

    /// Chains this iterator with another.
    fn chain<C>(self, chain: C) -> Chain<Self, C::Iter>
    where
        C: IntoParallelIterator<Item = Self::Item>,
    {
        Chain::new(self, chain.into_par_iter())
    }

    /// Folds each leaf of the parallel splitting tree with `fold_op`
    /// starting from `identity()`, yielding one accumulator per leaf as
    /// a new parallel iterator (usually combined with `reduce`).
    fn fold<T, ID, F>(self, identity: ID, fold_op: F) -> Fold<Self, ID, F>
    where
        F: Fn(T, Self::Item) -> T + Sync + Send,
        ID: Fn() -> T + Sync + Send,
        T: Send,
    {
        Fold::new(self, identity, fold_op)
    }

    /// Like [`fold`](Self::fold), cloning `init` per leaf.
    fn fold_with<F, T>(self, init: T, fold_op: F) -> FoldWith<Self, T, F>
    where
        F: Fn(T, Self::Item) -> T + Sync + Send,
        T: Send + Clone,
    {
        FoldWith::new(self, init, fold_op)
    }

    /// Reduces with `op`, returning `None` on an empty iterator.
    fn reduce_with<OP>(self, op: OP) -> Option<Self::Item>
    where
        OP: Fn(Self::Item, Self::Item) -> Self::Item + Sync + Send,
    {
        self.fold(
            || None,
            |opt_a, b| match opt_a {
                Some(a) => Some(op(a, b)),
                None => Some(b),
            },
        )
        .reduce(
            || None,
            |opt_a, opt_b| match (opt_a, opt_b) {
                (Some(a), Some(b)) => Some(op(a, b)),
                (Some(a), None) => Some(a),
                (None, Some(b)) => Some(b),
                (None, None) => None,
            },
        )
    }

    /// Multiplies the items (or anything `Product`-compatible).
    fn product<P>(self) -> P
    where
        P: Send + Product<Self::Item> + Product<P>,
    {
        product::product(self)
    }

    /// The minimum item, or `None` if empty.
    fn min(self) -> Option<Self::Item>
    where
        Self::Item: Ord,
    {
        self.reduce_with(Ord::min)
    }

    /// The maximum item, or `None` if empty.
    fn max(self) -> Option<Self::Item>
    where
        Self::Item: Ord,
    {
        self.reduce_with(Ord::max)
    }

    /// The item minimizing `compare`.
    fn min_by<F>(self, compare: F) -> Option<Self::Item>
    where
        F: Sync + Send + Fn(&Self::Item, &Self::Item) -> Ordering,
    {
        self.reduce_with(|a, b| match compare(&a, &b) {
            Ordering::Greater => b,
            _ => a,
        })
    }

    /// The item maximizing `compare`.
    fn max_by<F>(self, compare: F) -> Option<Self::Item>
    where
        F: Sync + Send + Fn(&Self::Item, &Self::Item) -> Ordering,
    {
        self.reduce_with(|a, b| match compare(&a, &b) {
            Ordering::Greater | Ordering::Equal => a,
            Ordering::Less => b,
        })
    }

    /// The item minimizing `key(item)`.
    fn min_by_key<K, F>(self, f: F) -> Option<Self::Item>
    where
        K: Ord + Send,
        F: Sync + Send + Fn(&Self::Item) -> K,
    {
        self.map(|x| (f(&x), x))
            .reduce_with(|a, b| if b.0 < a.0 { b } else { a })
            .map(|(_, x)| x)
    }

    /// The item maximizing `key(item)`.
    fn max_by_key<K, F>(self, f: F) -> Option<Self::Item>
    where
        K: Ord + Send,
        F: Sync + Send + Fn(&Self::Item) -> K,
    {
        self.map(|x| (f(&x), x))
            .reduce_with(|a, b| if b.0 > a.0 { b } else { a })
            .map(|(_, x)| x)
    }

    /// Finds *some* item matching `predicate` (not necessarily the
    /// first), short-circuiting other threads once found.
    fn find_any<P>(self, predicate: P) -> Option<Self::Item>
    where
        P: Fn(&Self::Item) -> bool + Sync + Send,
    {
        find::find_any(self, predicate)
    }

    /// True if any item matches.
    fn any<P>(self, predicate: P) -> bool
    where
        P: Fn(Self::Item) -> bool + Sync + Send,
    {
        self.map(predicate).find_any(bool::clone).is_some()
    }

    /// True if all items match.
    fn all<P>(self, predicate: P) -> bool
    where
        P: Fn(Self::Item) -> bool + Sync + Send,
    {
        !self.map(predicate).find_any(|&p| !p).is_some()
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

    /// Iterates over `(self item, other item)` tuples in lockstep,
    /// stopping at the shorter input.
    fn zip<Z>(self, zip_op: Z) -> Zip<Self, Z::Iter>
    where
        Z: IntoParallelIterator,
        Z::Iter: IndexedParallelIterator,
    {
        Zip::new(self, zip_op.into_par_iter())
    }

    /// Like [`zip`](Self::zip), but panics if the lengths differ.
    fn zip_eq<Z>(self, zip_op: Z) -> Zip<Self, Z::Iter>
    where
        Z: IntoParallelIterator,
        Z::Iter: IndexedParallelIterator,
    {
        let zip_op_iter = zip_op.into_par_iter();
        assert_eq!(
            self.len(),
            zip_op_iter.len(),
            "iterators must have the same length in zip_eq"
        );
        Zip::new(self, zip_op_iter)
    }

    /// Yields `(index, item)` pairs.
    fn enumerate(self) -> Enumerate<Self> {
        Enumerate::new(self)
    }

    /// Reverses the order of items.
    fn rev(self) -> Rev<Self> {
        Rev::new(self)
    }

    /// Skips the first `n` items.
    fn skip(self, n: usize) -> Skip<Self> {
        Skip::new(self, n)
    }

    /// Keeps only the first `n` items.
    fn take(self, n: usize) -> Take<Self> {
        Take::new(self, n)
    }

    /// Sets the minimum number of items processed per leaf (higher =
    /// less splitting overhead, coarser load balancing).
    fn with_min_len(self, min: usize) -> MinLen<Self> {
        MinLen::new(self, min)
    }

    /// Sets the maximum number of items processed per leaf.
    fn with_max_len(self, max: usize) -> MaxLen<Self> {
        MaxLen::new(self, max)
    }

    /// Finds the index of *some* item matching `predicate`.
    fn position_any<P>(self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool + Sync + Send,
    {
        self.map(predicate)
            .enumerate()
            .find_any(|&(_, p)| p)
            .map(|(i, _)| i)
    }
}
