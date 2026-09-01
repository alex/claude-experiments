//! The low-level "plumbing" that connects parallel iterators to the
//! work-stealing scheduler. Implement these traits to make your own type
//! iterable in parallel.
//!
//! The model (shared with rayon, whose architecture this follows) has two
//! halves:
//!
//! * A [`Producer`] describes *where items come from*: it can be split at
//!   an index into two producers, and at the leaves of the splitting tree
//!   it converts into an ordinary sequential [`Iterator`].
//! * A [`Consumer`] describes *where items go*: it can be split to mirror
//!   the producer, hands out a [`Folder`] at the leaves which consumes
//!   items one by one (or better: an entire sequential iterator at a time,
//!   via [`Folder::consume_iter`], which preserves internal iteration and
//!   thus autovectorization), and recombines results with a [`Reducer`].
//!
//! [`bridge`] connects the two with recursive [`join`]-based splitting.
//! Splitting is *adaptive*: we split enough to give every thread work,
//! and beyond that only when a piece is actually stolen (which signals
//! that other threads are idle).

use crate::join_context;
use crate::registry::current_num_threads;

/// Initial split budget multiplier (leaves ~= 2^ceil(log2(threads * this))).
const SPLITS_PER_THREAD: usize = 2;

/// The `ProducerCallback` trait is a kind of generic closure,
/// analogous to `FnOnce`, that is called back with the producer built
/// by [`IndexedParallelIterator::with_producer`]. This continuation style
/// is needed because the producer's concrete type is an implementation
/// detail of the iterator (it cannot appear in the method signature).
pub trait ProducerCallback<T> {
    type Output;
    fn callback<P>(self, producer: P) -> Self::Output
    where
        P: Producer<Item = T>;
}

/// A `Producer` is a splittable source of items for an indexed parallel
/// iterator.
pub trait Producer: Send + Sized {
    type Item;
    type IntoIter: Iterator<Item = Self::Item> + DoubleEndedIterator + ExactSizeIterator;

    /// Convert into a sequential iterator; called at the leaves of the
    /// splitting tree.
    fn into_iter(self) -> Self::IntoIter;

    /// Minimum number of items a leaf should process (see
    /// `with_min_len`). The bridge never splits pieces below this size.
    #[inline]
    fn min_len(&self) -> usize {
        1
    }

    /// Maximum number of items a leaf should process; pieces larger than
    /// this are always split further.
    #[inline]
    fn max_len(&self) -> usize {
        usize::MAX
    }

    /// Split into two producers, the first with `index` items.
    fn split_at(self, index: usize) -> (Self, Self);

    /// Fold this producer's items into `folder`. The default converts to
    /// the sequential iterator and feeds it whole to the folder, which
    /// preserves internal iteration.
    #[inline]
    fn fold_with<F>(self, folder: F) -> F
    where
        F: Folder<Self::Item>,
    {
        folder.consume_iter(self.into_iter())
    }
}

/// A splittable sink for items.
pub trait Consumer<Item>: Send + Sized {
    type Folder: Folder<Item, Result = Self::Result>;
    type Reducer: Reducer<Self::Result>;
    type Result: Send;

    /// Split into two consumers, mirroring `Producer::split_at`; also
    /// returns the reducer for recombining the two results.
    fn split_at(self, index: usize) -> (Self, Self, Self::Reducer);

    /// Convert into a folder, which sequentially consumes items.
    fn into_folder(self) -> Self::Folder;

    /// True if the consumer no longer needs items (short-circuiting
    /// operations like `find_any`); producers should stop as soon as
    /// possible.
    fn full(&self) -> bool;
}

/// A consumer that can additionally be split "off the left" an arbitrary
/// number of times, for driving un-indexed iterators where split
/// positions are not known in advance.
pub trait UnindexedConsumer<I>: Consumer<I> {
    /// Splits off a consumer for the "left" items; `self` keeps consuming
    /// the rest.
    fn split_off_left(&self) -> Self;

    /// A reducer for combining a left result with `self`'s result.
    fn to_reducer(&self) -> Self::Reducer;
}

/// Sequentially consumes items at a leaf of the splitting tree.
pub trait Folder<Item>: Sized {
    type Result;

    /// Consume one item.
    fn consume(self, item: Item) -> Self;

    /// Consume many items. **Performance-critical**: implementations
    /// should forward composed iterator adapters (e.g. `iter.map(f)`) to
    /// their base folder so that the entire leaf compiles down to one
    /// internally-iterated loop.
    #[inline]
    fn consume_iter<I>(mut self, iter: I) -> Self
    where
        I: IntoIterator<Item = Item>,
    {
        for item in iter {
            self = self.consume(item);
            if self.full() {
                break;
            }
        }
        self
    }

    /// Finish, yielding the result.
    fn complete(self) -> Self::Result;

    /// True if no more items should be consumed (short-circuiting).
    fn full(&self) -> bool;
}

/// Combines two adjacent results into one.
pub trait Reducer<Result> {
    fn reduce(self, left: Result, right: Result) -> Result;
}

/// A splittable source of items whose length is not known in advance;
/// splits happen at arbitrary (implementation-chosen) positions.
pub trait UnindexedProducer: Send + Sized {
    type Item;

    /// Split into two halves if possible (the second is `None` when this
    /// producer cannot usefully split further).
    fn split(self) -> (Self, Option<Self>);

    /// Sequentially fold the items into `folder`.
    fn fold_with<F>(self, folder: F) -> F
    where
        F: Folder<Self::Item>;
}

// //////////////////////////////////////////////////////////////////////
// Adaptive splitting

/// Steal-adaptive splitting policy. We aim for enough pieces to occupy
/// every thread; whenever a piece is observed to have been *stolen*
/// (executed on a different thread than the one that forked it), that is
/// evidence of idle threads, so the budget is replenished.
#[derive(Copy, Clone)]
struct Splitter {
    splits: usize,
}

impl Splitter {
    #[inline]
    fn new() -> Splitter {
        Splitter {
            splits: current_num_threads() * SPLITS_PER_THREAD,
        }
    }

    #[inline]
    fn try_split(&mut self, stolen: bool) -> bool {
        let Splitter { splits } = *self;
        if stolen {
            // This piece was stolen: some thread was idle. Replenish the
            // split budget so the thief has more to share.
            self.splits = Ord::max(current_num_threads(), self.splits / 2);
            true
        } else if splits > 0 {
            self.splits /= 2;
            true
        } else {
            false
        }
    }
}

/// A splitter that additionally respects min/max piece lengths.
#[derive(Copy, Clone)]
struct LengthSplitter {
    inner: Splitter,
    min: usize,
}

impl LengthSplitter {
    #[inline]
    fn new(min: usize, max: usize, len: usize) -> LengthSplitter {
        let mut splitter = LengthSplitter {
            inner: Splitter::new(),
            min: Ord::max(min, 1),
        };
        // Ensure we split at least enough that pieces respect `max`.
        let min_splits = len / Ord::max(max, 1);
        if min_splits > splitter.inner.splits {
            splitter.inner.splits = min_splits;
        }
        splitter
    }

    #[inline]
    fn try_split(&mut self, len: usize, stolen: bool) -> bool {
        // Only split pieces that stay >= min on both sides.
        len / 2 >= self.min && self.inner.try_split(stolen)
    }
}

// //////////////////////////////////////////////////////////////////////
// Bridges

/// Drives an indexed parallel iterator into a consumer: the standard way
/// to implement `IndexedParallelIterator::drive` /
/// `ParallelIterator::drive_unindexed` for indexed sources.
pub fn bridge<I, C>(par_iter: I, consumer: C) -> C::Result
where
    I: crate::iter::IndexedParallelIterator,
    C: Consumer<I::Item>,
{
    let len = par_iter.len();
    return par_iter.with_producer(Callback { len, consumer });

    struct Callback<C> {
        len: usize,
        consumer: C,
    }

    impl<C, T> ProducerCallback<T> for Callback<C>
    where
        C: Consumer<T>,
    {
        type Output = C::Result;
        fn callback<P>(self, producer: P) -> C::Result
        where
            P: Producer<Item = T>,
        {
            bridge_producer_consumer(self.len, producer, self.consumer)
        }
    }
}

/// Connects a `Producer` and a `Consumer` with adaptive parallel
/// splitting.
pub fn bridge_producer_consumer<P, C>(len: usize, producer: P, consumer: C) -> C::Result
where
    P: Producer,
    C: Consumer<P::Item>,
{
    let splitter = LengthSplitter::new(producer.min_len(), producer.max_len(), len);
    return helper(len, false, splitter, producer, consumer);

    fn helper<P, C>(
        len: usize,
        migrated: bool,
        mut splitter: LengthSplitter,
        producer: P,
        consumer: C,
    ) -> C::Result
    where
        P: Producer,
        C: Consumer<P::Item>,
    {
        if consumer.full() {
            consumer.into_folder().complete()
        } else if splitter.try_split(len, migrated) {
            let mid = len / 2;
            let (left_producer, right_producer) = producer.split_at(mid);
            let (left_consumer, right_consumer, reducer) = consumer.split_at(mid);
            let (left_result, right_result) = join_context(
                |context| {
                    helper(
                        mid,
                        context.migrated(),
                        splitter,
                        left_producer,
                        left_consumer,
                    )
                },
                |context| {
                    helper(
                        len - mid,
                        context.migrated(),
                        splitter,
                        right_producer,
                        right_consumer,
                    )
                },
            );
            reducer.reduce(left_result, right_result)
        } else {
            producer.fold_with(consumer.into_folder()).complete()
        }
    }
}

/// Drives an unindexed producer into an unindexed consumer, splitting
/// adaptively at producer-chosen positions.
pub fn bridge_unindexed<P, C>(producer: P, consumer: C) -> C::Result
where
    P: UnindexedProducer,
    C: UnindexedConsumer<P::Item>,
{
    let splitter = Splitter::new();
    bridge_unindexed_producer_consumer(false, splitter, producer, consumer)
}

fn bridge_unindexed_producer_consumer<P, C>(
    migrated: bool,
    mut splitter: Splitter,
    producer: P,
    consumer: C,
) -> C::Result
where
    P: UnindexedProducer,
    C: UnindexedConsumer<P::Item>,
{
    if consumer.full() {
        consumer.into_folder().complete()
    } else if splitter.try_split(migrated) {
        match producer.split() {
            (left_producer, Some(right_producer)) => {
                let (reducer, left_consumer, right_consumer) =
                    (consumer.to_reducer(), consumer.split_off_left(), consumer);
                let (left_result, right_result) = join_context(
                    |context| {
                        bridge_unindexed_producer_consumer(
                            context.migrated(),
                            splitter,
                            left_producer,
                            left_consumer,
                        )
                    },
                    |context| {
                        bridge_unindexed_producer_consumer(
                            context.migrated(),
                            splitter,
                            right_producer,
                            right_consumer,
                        )
                    },
                );
                reducer.reduce(left_result, right_result)
            }
            (producer, None) => producer.fold_with(consumer.into_folder()).complete(),
        }
    } else {
        producer.fold_with(consumer.into_folder()).complete()
    }
}
