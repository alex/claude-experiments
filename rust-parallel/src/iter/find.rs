//! Short-circuiting searches: `find_any`, `any`, `all`.

use super::plumbing::{Consumer, Folder, Reducer, UnindexedConsumer};
use super::ParallelIterator;
use std::sync::atomic::{AtomicBool, Ordering};

pub(super) fn find_any<I, P>(pi: I, find_op: P) -> Option<I::Item>
where
    I: ParallelIterator,
    P: Fn(&I::Item) -> bool + Sync,
{
    let found = AtomicBool::new(false);
    let consumer = FindConsumer {
        find_op: &find_op,
        found: &found,
    };
    pi.drive_unindexed(consumer)
}

struct FindConsumer<'p, P> {
    find_op: &'p P,
    found: &'p AtomicBool,
}

impl<'p, T, P> Consumer<T> for FindConsumer<'p, P>
where
    T: Send,
    P: Fn(&T) -> bool + Sync,
{
    type Folder = FindFolder<'p, T, P>;
    type Reducer = FindReducer;
    type Result = Option<T>;

    fn split_at(self, _index: usize) -> (Self, Self, Self::Reducer) {
        (
            FindConsumer { ..self },
            FindConsumer { ..self },
            FindReducer,
        )
    }

    fn into_folder(self) -> Self::Folder {
        FindFolder {
            find_op: self.find_op,
            found: self.found,
            item: None,
        }
    }

    fn full(&self) -> bool {
        self.found.load(Ordering::Relaxed)
    }
}

impl<'p, P> Copy for FindConsumer<'p, P> {}
impl<'p, P> Clone for FindConsumer<'p, P> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'p, T, P> UnindexedConsumer<T> for FindConsumer<'p, P>
where
    T: Send,
    P: Fn(&T) -> bool + Sync,
{
    fn split_off_left(&self) -> Self {
        *self
    }

    fn to_reducer(&self) -> Self::Reducer {
        FindReducer
    }
}

struct FindFolder<'p, T, P> {
    find_op: &'p P,
    found: &'p AtomicBool,
    item: Option<T>,
}

impl<'p, T, P> Folder<T> for FindFolder<'p, T, P>
where
    P: Fn(&T) -> bool + 'p,
{
    type Result = Option<T>;

    #[inline]
    fn consume(mut self, item: T) -> Self {
        if (self.find_op)(&item) {
            self.found.store(true, Ordering::Relaxed);
            self.item = Some(item);
        }
        self
    }

    #[inline]
    fn consume_iter<I>(mut self, iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        // Check the shared flag only periodically so the hot search loop
        // stays free of atomic loads.
        const CHECK_EVERY: usize = 128;
        let mut iter = iter.into_iter();
        loop {
            if self.full() {
                break;
            }
            let mut n = 0usize;
            for item in iter.by_ref() {
                n += 1;
                if (self.find_op)(&item) {
                    self.found.store(true, Ordering::Relaxed);
                    self.item = Some(item);
                    return self;
                }
                if n == CHECK_EVERY {
                    break;
                }
            }
            if n < CHECK_EVERY {
                break; // iterator exhausted
            }
        }
        self
    }

    fn complete(self) -> Self::Result {
        self.item
    }

    fn full(&self) -> bool {
        self.item.is_some() || self.found.load(Ordering::Relaxed)
    }
}

struct FindReducer;

impl<T> Reducer<Option<T>> for FindReducer {
    fn reduce(self, left: Option<T>, right: Option<T>) -> Option<T> {
        left.or(right)
    }
}
