use super::plumbing::{Consumer, Folder, Reducer, UnindexedConsumer};
use super::ParallelIterator;

pub(super) fn count<I>(pi: I) -> usize
where
    I: ParallelIterator,
{
    pi.drive_unindexed(CountConsumer)
}

struct CountConsumer;

impl<T> Consumer<T> for CountConsumer {
    type Folder = CountFolder;
    type Reducer = CountConsumer;
    type Result = usize;

    fn split_at(self, _index: usize) -> (Self, Self, Self::Reducer) {
        (CountConsumer, CountConsumer, CountConsumer)
    }

    fn into_folder(self) -> Self::Folder {
        CountFolder { count: 0 }
    }

    fn full(&self) -> bool {
        false
    }
}

impl<T> UnindexedConsumer<T> for CountConsumer {
    fn split_off_left(&self) -> Self {
        CountConsumer
    }

    fn to_reducer(&self) -> Self::Reducer {
        CountConsumer
    }
}

impl Reducer<usize> for CountConsumer {
    #[inline]
    fn reduce(self, left: usize, right: usize) -> usize {
        left + right
    }
}

struct CountFolder {
    count: usize,
}

impl<T> Folder<T> for CountFolder {
    type Result = usize;

    #[inline]
    fn consume(mut self, _item: T) -> Self {
        self.count += 1;
        self
    }

    #[inline]
    fn consume_iter<I>(mut self, iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        self.count += iter.into_iter().count();
        self
    }

    fn complete(self) -> usize {
        self.count
    }

    fn full(&self) -> bool {
        false
    }
}
