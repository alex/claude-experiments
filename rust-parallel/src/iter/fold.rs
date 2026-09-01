use super::plumbing::{Consumer, Folder, UnindexedConsumer};
use super::ParallelIterator;

/// `Fold` is an iterator over the per-leaf accumulated results of a fold
/// operation. Created by [`ParallelIterator::fold`].
#[derive(Debug, Clone)]
pub struct Fold<I, ID, F> {
    base: I,
    identity: ID,
    fold_op: F,
}

impl<I, ID, F> Fold<I, ID, F> {
    pub(super) fn new(base: I, identity: ID, fold_op: F) -> Self {
        Fold {
            base,
            identity,
            fold_op,
        }
    }
}

impl<U, I, ID, F> ParallelIterator for Fold<I, ID, F>
where
    I: ParallelIterator,
    F: Fn(U, I::Item) -> U + Sync + Send,
    ID: Fn() -> U + Sync + Send,
    U: Send,
{
    type Item = U;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        let consumer1 = FoldConsumer {
            base: consumer,
            fold_op: &self.fold_op,
            identity: &self.identity,
        };
        self.base.drive_unindexed(consumer1)
    }
}

struct FoldConsumer<'c, C, ID, F> {
    base: C,
    fold_op: &'c F,
    identity: &'c ID,
}

impl<'r, U, T, C, ID, F> Consumer<T> for FoldConsumer<'r, C, ID, F>
where
    C: Consumer<U>,
    F: Fn(U, T) -> U + Sync,
    ID: Fn() -> U + Sync,
    U: Send,
{
    type Folder = FoldFolder<'r, C::Folder, U, F>;
    type Reducer = C::Reducer;
    type Result = C::Result;

    fn split_at(self, index: usize) -> (Self, Self, Self::Reducer) {
        let (left, right, reducer) = self.base.split_at(index);
        (
            FoldConsumer {
                base: left,
                fold_op: self.fold_op,
                identity: self.identity,
            },
            FoldConsumer {
                base: right,
                fold_op: self.fold_op,
                identity: self.identity,
            },
            reducer,
        )
    }

    fn into_folder(self) -> Self::Folder {
        FoldFolder {
            base: self.base.into_folder(),
            fold_op: self.fold_op,
            item: (self.identity)(),
        }
    }

    fn full(&self) -> bool {
        self.base.full()
    }
}

impl<'r, U, T, C, ID, F> UnindexedConsumer<T> for FoldConsumer<'r, C, ID, F>
where
    C: UnindexedConsumer<U>,
    F: Fn(U, T) -> U + Sync,
    ID: Fn() -> U + Sync,
    U: Send,
{
    fn split_off_left(&self) -> Self {
        FoldConsumer {
            base: self.base.split_off_left(),
            fold_op: self.fold_op,
            identity: self.identity,
        }
    }

    fn to_reducer(&self) -> Self::Reducer {
        self.base.to_reducer()
    }
}

struct FoldFolder<'r, C, U, F> {
    base: C,
    fold_op: &'r F,
    item: U,
}

impl<'r, U, T, C, F> Folder<T> for FoldFolder<'r, C, U, F>
where
    C: Folder<U>,
    F: Fn(U, T) -> U + Sync,
{
    type Result = C::Result;

    #[inline]
    fn consume(self, item: T) -> Self {
        let item = (self.fold_op)(self.item, item);
        FoldFolder {
            base: self.base,
            fold_op: self.fold_op,
            item,
        }
    }

    #[inline]
    fn consume_iter<I>(self, iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let FoldFolder {
            base,
            fold_op,
            item,
        } = self;
        // Internal iteration for the accumulation loop.
        let item = iter.into_iter().fold(item, fold_op);
        FoldFolder {
            base,
            fold_op,
            item,
        }
    }

    fn complete(self) -> C::Result {
        self.base.consume(self.item).complete()
    }

    fn full(&self) -> bool {
        self.base.full()
    }
}

// ///////////////////////////////////////////////////////////////////////
// fold_with: like fold, but cloning an initial value per leaf.

/// Created by [`ParallelIterator::fold_with`].
#[derive(Debug, Clone)]
pub struct FoldWith<I, U, F> {
    base: I,
    item: U,
    fold_op: F,
}

impl<I, U, F> FoldWith<I, U, F> {
    pub(super) fn new(base: I, item: U, fold_op: F) -> Self {
        FoldWith {
            base,
            item,
            fold_op,
        }
    }
}

impl<U, I, F> ParallelIterator for FoldWith<I, U, F>
where
    I: ParallelIterator,
    F: Fn(U, I::Item) -> U + Sync + Send,
    U: Send + Clone,
{
    type Item = U;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        let consumer1 = FoldWithConsumer {
            base: consumer,
            item: self.item,
            fold_op: &self.fold_op,
        };
        self.base.drive_unindexed(consumer1)
    }
}

struct FoldWithConsumer<'c, C, U, F> {
    base: C,
    item: U,
    fold_op: &'c F,
}

impl<'r, U, T, C, F> Consumer<T> for FoldWithConsumer<'r, C, U, F>
where
    C: Consumer<U>,
    F: Fn(U, T) -> U + Sync,
    U: Send + Clone,
{
    type Folder = FoldFolder<'r, C::Folder, U, F>;
    type Reducer = C::Reducer;
    type Result = C::Result;

    fn split_at(self, index: usize) -> (Self, Self, Self::Reducer) {
        let (left, right, reducer) = self.base.split_at(index);
        (
            FoldWithConsumer {
                base: left,
                item: self.item.clone(),
                fold_op: self.fold_op,
            },
            FoldWithConsumer {
                base: right,
                item: self.item,
                fold_op: self.fold_op,
            },
            reducer,
        )
    }

    fn into_folder(self) -> Self::Folder {
        FoldFolder {
            base: self.base.into_folder(),
            fold_op: self.fold_op,
            item: self.item,
        }
    }

    fn full(&self) -> bool {
        self.base.full()
    }
}

impl<'r, U, T, C, F> UnindexedConsumer<T> for FoldWithConsumer<'r, C, U, F>
where
    C: UnindexedConsumer<U>,
    F: Fn(U, T) -> U + Sync,
    U: Send + Clone,
{
    fn split_off_left(&self) -> Self {
        FoldWithConsumer {
            base: self.base.split_off_left(),
            item: self.item.clone(),
            fold_op: self.fold_op,
        }
    }

    fn to_reducer(&self) -> Self::Reducer {
        self.base.to_reducer()
    }
}
