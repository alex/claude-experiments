use super::plumbing::{Consumer, Folder, Producer, ProducerCallback, Reducer, UnindexedConsumer};
use super::{IndexedParallelIterator, ParallelIterator};

/// `Chain` concatenates two iterators. Created by
/// [`ParallelIterator::chain`].
#[derive(Debug, Clone)]
pub struct Chain<A, B> {
    a: A,
    b: B,
}

impl<A, B> Chain<A, B> {
    pub(super) fn new(a: A, b: B) -> Self {
        Chain { a, b }
    }
}

impl<A, B> ParallelIterator for Chain<A, B>
where
    A: ParallelIterator,
    B: ParallelIterator<Item = A::Item>,
{
    type Item = A::Item;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        // Drive each half into its own split of the consumer. The two
        // `drive` calls run one after the other, but each parallelizes
        // internally (and the first can be stolen from while the caller
        // works on the second).
        let Chain { a, b } = self;
        let (left, right, reducer) = if let Some(len) = a.opt_len() {
            consumer.split_at(len)
        } else {
            let reducer = consumer.to_reducer();
            (consumer.split_off_left(), consumer, reducer)
        };
        let a_result = a.drive_unindexed(left);
        let b_result = b.drive_unindexed(right);
        reducer.reduce(a_result, b_result)
    }

    fn opt_len(&self) -> Option<usize> {
        self.a.opt_len()?.checked_add(self.b.opt_len()?)
    }
}

impl<A, B> IndexedParallelIterator for Chain<A, B>
where
    A: IndexedParallelIterator,
    B: IndexedParallelIterator<Item = A::Item>,
{
    fn drive<C>(self, consumer: C) -> C::Result
    where
        C: Consumer<Self::Item>,
    {
        let Chain { a, b } = self;
        let (left, right, reducer) = consumer.split_at(a.len());
        let a_result = a.drive(left);
        let b_result = b.drive(right);
        reducer.reduce(a_result, b_result)
    }

    fn len(&self) -> usize {
        self.a
            .len()
            .checked_add(self.b.len())
            .expect("overflow in Chain::len")
    }

    fn with_producer<CB>(self, callback: CB) -> CB::Output
    where
        CB: ProducerCallback<Self::Item>,
    {
        let a_len = self.a.len();
        return self.a.with_producer(CallbackA {
            callback,
            a_len,
            b: self.b,
        });

        struct CallbackA<CB, B> {
            callback: CB,
            a_len: usize,
            b: B,
        }

        impl<CB, B, T> ProducerCallback<T> for CallbackA<CB, B>
        where
            B: IndexedParallelIterator<Item = T>,
            CB: ProducerCallback<T>,
            T: Send,
        {
            type Output = CB::Output;

            fn callback<A>(self, a_producer: A) -> Self::Output
            where
                A: Producer<Item = T>,
            {
                self.b.with_producer(CallbackB {
                    callback: self.callback,
                    a_len: self.a_len,
                    a_producer,
                })
            }
        }

        struct CallbackB<CB, A> {
            callback: CB,
            a_len: usize,
            a_producer: A,
        }

        impl<CB, A, T> ProducerCallback<T> for CallbackB<CB, A>
        where
            A: Producer<Item = T>,
            CB: ProducerCallback<T>,
            T: Send,
        {
            type Output = CB::Output;

            fn callback<B>(self, b_producer: B) -> Self::Output
            where
                B: Producer<Item = T>,
            {
                self.callback.callback(ChainProducer {
                    a_len: self.a_len,
                    a: self.a_producer,
                    b: b_producer,
                })
            }
        }
    }
}

struct ChainProducer<A, B>
where
    A: Producer,
    B: Producer<Item = A::Item>,
{
    a_len: usize,
    a: A,
    b: B,
}

impl<A, B> Producer for ChainProducer<A, B>
where
    A: Producer,
    B: Producer<Item = A::Item>,
{
    type Item = A::Item;
    type IntoIter = ChainSeq<A::IntoIter, B::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        ChainSeq {
            a: self.a.into_iter(),
            b: self.b.into_iter(),
        }
    }

    fn min_len(&self) -> usize {
        Ord::max(self.a.min_len(), self.b.min_len())
    }

    fn max_len(&self) -> usize {
        Ord::min(self.a.max_len(), self.b.max_len())
    }

    fn split_at(self, index: usize) -> (Self, Self) {
        if index <= self.a_len {
            let a_rem = self.a_len - index;
            let (a_left, a_right) = self.a.split_at(index);
            let (b_left, b_right) = self.b.split_at(0);
            (
                ChainProducer {
                    a_len: index,
                    a: a_left,
                    b: b_left,
                },
                ChainProducer {
                    a_len: a_rem,
                    a: a_right,
                    b: b_right,
                },
            )
        } else {
            let (a_left, a_right) = self.a.split_at(self.a_len);
            let (b_left, b_right) = self.b.split_at(index - self.a_len);
            (
                ChainProducer {
                    a_len: self.a_len,
                    a: a_left,
                    b: b_left,
                },
                ChainProducer {
                    a_len: 0,
                    a: a_right,
                    b: b_right,
                },
            )
        }
    }

    fn fold_with<F>(self, folder: F) -> F
    where
        F: Folder<Self::Item>,
    {
        let folder = self.a.fold_with(folder);
        if folder.full() {
            folder
        } else {
            self.b.fold_with(folder)
        }
    }
}

/// Sequential chain with `ExactSizeIterator` support (std's `Chain`
/// deliberately doesn't implement it; our producer lengths are already
/// validated to fit `usize`).
pub(super) struct ChainSeq<A, B> {
    a: A,
    b: B,
}

impl<A, B> Iterator for ChainSeq<A, B>
where
    A: ExactSizeIterator,
    B: ExactSizeIterator<Item = A::Item>,
{
    type Item = A::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self.a.next() {
            Some(x) => Some(x),
            None => self.b.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    #[inline]
    fn fold<Acc, F>(self, init: Acc, mut f: F) -> Acc
    where
        F: FnMut(Acc, Self::Item) -> Acc,
    {
        let acc = self.a.fold(init, &mut f);
        self.b.fold(acc, f)
    }
}

impl<A, B> DoubleEndedIterator for ChainSeq<A, B>
where
    A: ExactSizeIterator + DoubleEndedIterator,
    B: ExactSizeIterator<Item = A::Item> + DoubleEndedIterator,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.b.next_back() {
            Some(x) => Some(x),
            None => self.a.next_back(),
        }
    }
}

impl<A, B> ExactSizeIterator for ChainSeq<A, B>
where
    A: ExactSizeIterator,
    B: ExactSizeIterator<Item = A::Item>,
{
    fn len(&self) -> usize {
        self.a.len() + self.b.len()
    }
}
