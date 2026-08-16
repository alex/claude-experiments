//! Parallel iterators over `Option<T>` and `Result<T, E>` (0 or 1 items).

use crate::iter::plumbing::{bridge, Consumer, Producer, ProducerCallback, UnindexedConsumer};
use crate::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};

/// Parallel iterator over an `Option`.
#[derive(Debug, Clone)]
pub struct IntoIter<T: Send> {
    opt: Option<T>,
}

impl<T: Send> IntoParallelIterator for Option<T> {
    type Item = T;
    type Iter = IntoIter<T>;

    fn into_par_iter(self) -> Self::Iter {
        IntoIter { opt: self }
    }
}

impl<'a, T: Sync> IntoParallelIterator for &'a Option<T> {
    type Item = &'a T;
    type Iter = IntoIter<&'a T>;

    fn into_par_iter(self) -> Self::Iter {
        IntoIter {
            opt: self.as_ref(),
        }
    }
}

impl<'a, T: Send> IntoParallelIterator for &'a mut Option<T> {
    type Item = &'a mut T;
    type Iter = IntoIter<&'a mut T>;

    fn into_par_iter(self) -> Self::Iter {
        IntoIter {
            opt: self.as_mut(),
        }
    }
}

impl<T: Send> ParallelIterator for IntoIter<T> {
    type Item = T;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn opt_len(&self) -> Option<usize> {
        Some(self.len())
    }
}

impl<T: Send> IndexedParallelIterator for IntoIter<T> {
    fn len(&self) -> usize {
        match self.opt {
            Some(_) => 1,
            None => 0,
        }
    }

    fn drive<C>(self, consumer: C) -> C::Result
    where
        C: Consumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn with_producer<CB>(self, callback: CB) -> CB::Output
    where
        CB: ProducerCallback<Self::Item>,
    {
        callback.callback(OptionProducer { opt: self.opt })
    }
}

struct OptionProducer<T: Send> {
    opt: Option<T>,
}

impl<T: Send> Producer for OptionProducer<T> {
    type Item = T;
    type IntoIter = std::option::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.opt.into_iter()
    }

    fn split_at(self, index: usize) -> (Self, Self) {
        debug_assert!(index <= 1);
        let none = OptionProducer { opt: None };
        if index == 0 {
            (none, self)
        } else {
            (self, none)
        }
    }
}

// //////////////////////////////////////////////////////////////////////
// Result: iterates the Ok value, if any.

impl<T: Send, E> IntoParallelIterator for Result<T, E> {
    type Item = T;
    type Iter = IntoIter<T>;

    fn into_par_iter(self) -> Self::Iter {
        IntoIter { opt: self.ok() }
    }
}

impl<'a, T: Sync, E> IntoParallelIterator for &'a Result<T, E> {
    type Item = &'a T;
    type Iter = IntoIter<&'a T>;

    fn into_par_iter(self) -> Self::Iter {
        IntoIter {
            opt: self.as_ref().ok(),
        }
    }
}

impl<'a, T: Send, E> IntoParallelIterator for &'a mut Result<T, E> {
    type Item = &'a mut T;
    type Iter = IntoIter<&'a mut T>;

    fn into_par_iter(self) -> Self::Iter {
        IntoIter {
            opt: self.as_mut().ok(),
        }
    }
}
