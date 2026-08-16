use super::plumbing::{Consumer, Folder, Reducer, UnindexedConsumer};
use super::ParallelIterator;
use std::iter::{self, Sum};
use std::marker::PhantomData;

pub(super) fn sum<PI, S>(pi: PI) -> S
where
    PI: ParallelIterator,
    S: Send + Sum<PI::Item> + Sum<S>,
{
    pi.drive_unindexed(SumConsumer(PhantomData))
}

/// Combine two partial sums.
#[inline]
fn add<T: Sum>(left: T, right: T) -> T {
    [left, right].into_iter().sum()
}

struct SumConsumer<S: Send>(PhantomData<S>);

impl<S: Send> SumConsumer<S> {
    fn new() -> Self {
        SumConsumer(PhantomData)
    }
}

impl<S, T> Consumer<T> for SumConsumer<S>
where
    S: Send + Sum<T> + Sum<S>,
{
    type Folder = SumFolder<S>;
    type Reducer = SumConsumer<S>;
    type Result = S;

    fn split_at(self, _index: usize) -> (Self, Self, Self::Reducer) {
        (SumConsumer::new(), SumConsumer::new(), SumConsumer::new())
    }

    fn into_folder(self) -> Self::Folder {
        SumFolder {
            sum: iter::empty::<T>().sum(),
        }
    }

    fn full(&self) -> bool {
        false
    }
}

impl<S, T> UnindexedConsumer<T> for SumConsumer<S>
where
    S: Send + Sum<T> + Sum<S>,
{
    fn split_off_left(&self) -> Self {
        SumConsumer::new()
    }

    fn to_reducer(&self) -> Self::Reducer {
        SumConsumer::new()
    }
}

impl<S> Reducer<S> for SumConsumer<S>
where
    S: Send + Sum,
{
    #[inline]
    fn reduce(self, left: S, right: S) -> S {
        add(left, right)
    }
}

struct SumFolder<S> {
    sum: S,
}

impl<S, T> Folder<T> for SumFolder<S>
where
    S: Sum<T> + Sum<S>,
{
    type Result = S;

    #[inline]
    fn consume(self, item: T) -> Self {
        SumFolder {
            sum: add(self.sum, iter::once(item).sum()),
        }
    }

    #[inline]
    fn consume_iter<I>(self, iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        // One internally-iterated `sum` per leaf: this is the loop LLVM
        // vectorizes.
        SumFolder {
            sum: add(self.sum, iter.into_iter().sum()),
        }
    }

    fn complete(self) -> S {
        self.sum
    }

    fn full(&self) -> bool {
        false
    }
}
