use super::plumbing::{Consumer, Folder, UnindexedConsumer};
use super::ParallelIterator;

/// `FilterMap` creates an iterator that uses `filter_op` to both filter
/// and map elements. Created by [`ParallelIterator::filter_map`].
#[derive(Debug, Clone)]
pub struct FilterMap<I, P> {
    base: I,
    filter_op: P,
}

impl<I, P> FilterMap<I, P> {
    pub(super) fn new(base: I, filter_op: P) -> Self {
        FilterMap { base, filter_op }
    }
}

impl<I, P, R> ParallelIterator for FilterMap<I, P>
where
    I: ParallelIterator,
    P: Fn(I::Item) -> Option<R> + Sync + Send,
    R: Send,
{
    type Item = R;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        let consumer1 = FilterMapConsumer::new(consumer, &self.filter_op);
        self.base.drive_unindexed(consumer1)
    }
}

struct FilterMapConsumer<'p, C, P> {
    base: C,
    filter_op: &'p P,
}

impl<'p, C, P> FilterMapConsumer<'p, C, P> {
    fn new(base: C, filter_op: &'p P) -> Self {
        FilterMapConsumer { base, filter_op }
    }
}

impl<'p, T, U, C, P> Consumer<T> for FilterMapConsumer<'p, C, P>
where
    C: Consumer<U>,
    P: Fn(T) -> Option<U> + Sync + 'p,
{
    type Folder = FilterMapFolder<'p, C::Folder, P>;
    type Reducer = C::Reducer;
    type Result = C::Result;

    fn split_at(self, index: usize) -> (Self, Self, Self::Reducer) {
        let (left, right, reducer) = self.base.split_at(index);
        (
            FilterMapConsumer::new(left, self.filter_op),
            FilterMapConsumer::new(right, self.filter_op),
            reducer,
        )
    }

    fn into_folder(self) -> Self::Folder {
        let base = self.base.into_folder();
        FilterMapFolder {
            base,
            filter_op: self.filter_op,
        }
    }

    fn full(&self) -> bool {
        self.base.full()
    }
}

impl<'p, T, U, C, P> UnindexedConsumer<T> for FilterMapConsumer<'p, C, P>
where
    C: UnindexedConsumer<U>,
    P: Fn(T) -> Option<U> + Sync + 'p,
{
    fn split_off_left(&self) -> Self {
        FilterMapConsumer::new(self.base.split_off_left(), self.filter_op)
    }

    fn to_reducer(&self) -> Self::Reducer {
        self.base.to_reducer()
    }
}

struct FilterMapFolder<'p, C, P> {
    base: C,
    filter_op: &'p P,
}

impl<'p, T, U, C, P> Folder<T> for FilterMapFolder<'p, C, P>
where
    C: Folder<U>,
    P: Fn(T) -> Option<U> + Sync + 'p,
{
    type Result = C::Result;

    #[inline]
    fn consume(self, item: T) -> Self {
        let filter_op = self.filter_op;
        if let Some(mapped_item) = filter_op(item) {
            let base = self.base.consume(mapped_item);
            FilterMapFolder { base, filter_op }
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
        self.base = self
            .base
            .consume_iter(iter.into_iter().filter_map(filter_op));
        self
    }

    fn complete(self) -> C::Result {
        self.base.complete()
    }

    fn full(&self) -> bool {
        self.base.full()
    }
}
