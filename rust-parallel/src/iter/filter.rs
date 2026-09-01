use super::plumbing::{Consumer, Folder, UnindexedConsumer};
use super::ParallelIterator;

/// `Filter` takes a predicate and filters out elements that don't match.
/// Created by [`ParallelIterator::filter`].
#[derive(Debug, Clone)]
pub struct Filter<I, P> {
    base: I,
    filter_op: P,
}

impl<I, P> Filter<I, P> {
    pub(super) fn new(base: I, filter_op: P) -> Self {
        Filter { base, filter_op }
    }
}

impl<I, P> ParallelIterator for Filter<I, P>
where
    I: ParallelIterator,
    P: Fn(&I::Item) -> bool + Sync + Send,
{
    type Item = I::Item;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        let consumer1 = FilterConsumer::new(consumer, &self.filter_op);
        self.base.drive_unindexed(consumer1)
    }
}

struct FilterConsumer<'p, C, P> {
    base: C,
    filter_op: &'p P,
}

impl<'p, C, P> FilterConsumer<'p, C, P> {
    fn new(base: C, filter_op: &'p P) -> Self {
        FilterConsumer { base, filter_op }
    }
}

impl<'p, T, C, P: 'p> Consumer<T> for FilterConsumer<'p, C, P>
where
    C: Consumer<T>,
    P: Fn(&T) -> bool + Sync,
{
    type Folder = FilterFolder<'p, C::Folder, P>;
    type Reducer = C::Reducer;
    type Result = C::Result;

    fn split_at(self, index: usize) -> (Self, Self, Self::Reducer) {
        let (left, right, reducer) = self.base.split_at(index);
        (
            FilterConsumer::new(left, self.filter_op),
            FilterConsumer::new(right, self.filter_op),
            reducer,
        )
    }

    fn into_folder(self) -> Self::Folder {
        FilterFolder {
            base: self.base.into_folder(),
            filter_op: self.filter_op,
        }
    }

    fn full(&self) -> bool {
        self.base.full()
    }
}

impl<'p, T, C, P: 'p> UnindexedConsumer<T> for FilterConsumer<'p, C, P>
where
    C: UnindexedConsumer<T>,
    P: Fn(&T) -> bool + Sync,
{
    fn split_off_left(&self) -> Self {
        FilterConsumer::new(self.base.split_off_left(), self.filter_op)
    }

    fn to_reducer(&self) -> Self::Reducer {
        self.base.to_reducer()
    }
}

struct FilterFolder<'p, C, P> {
    base: C,
    filter_op: &'p P,
}

impl<'p, C, P, T> Folder<T> for FilterFolder<'p, C, P>
where
    C: Folder<T>,
    P: Fn(&T) -> bool + 'p,
{
    type Result = C::Result;

    #[inline]
    fn consume(self, item: T) -> Self {
        let filter_op = self.filter_op;
        if filter_op(&item) {
            let base = self.base.consume(item);
            FilterFolder { base, filter_op }
        } else {
            self
        }
    }

    #[inline]
    fn consume_iter<I>(mut self, iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let filter_op = self.filter_op;
        // Fuse the filter into the sequential iterator chain.
        self.base = self.base.consume_iter(iter.into_iter().filter(filter_op));
        self
    }

    fn complete(self) -> Self::Result {
        self.base.complete()
    }

    fn full(&self) -> bool {
        self.base.full()
    }
}
