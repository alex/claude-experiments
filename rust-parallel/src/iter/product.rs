use super::plumbing::{Consumer, Folder, Reducer, UnindexedConsumer};
use super::ParallelIterator;
use std::iter::{self, Product};
use std::marker::PhantomData;

pub(super) fn product<PI, P>(pi: PI) -> P
where
    PI: ParallelIterator,
    P: Send + Product<PI::Item> + Product<P>,
{
    pi.drive_unindexed(ProductConsumer(PhantomData))
}

#[inline]
fn mul<T: Product>(left: T, right: T) -> T {
    [left, right].into_iter().product()
}

struct ProductConsumer<P: Send>(PhantomData<P>);

impl<P: Send> ProductConsumer<P> {
    fn new() -> Self {
        ProductConsumer(PhantomData)
    }
}

impl<P, T> Consumer<T> for ProductConsumer<P>
where
    P: Send + Product<T> + Product<P>,
{
    type Folder = ProductFolder<P>;
    type Reducer = ProductConsumer<P>;
    type Result = P;

    fn split_at(self, _index: usize) -> (Self, Self, Self::Reducer) {
        (
            ProductConsumer::new(),
            ProductConsumer::new(),
            ProductConsumer::new(),
        )
    }

    fn into_folder(self) -> Self::Folder {
        ProductFolder {
            product: iter::empty::<T>().product(),
        }
    }

    fn full(&self) -> bool {
        false
    }
}

impl<P, T> UnindexedConsumer<T> for ProductConsumer<P>
where
    P: Send + Product<T> + Product<P>,
{
    fn split_off_left(&self) -> Self {
        ProductConsumer::new()
    }

    fn to_reducer(&self) -> Self::Reducer {
        ProductConsumer::new()
    }
}

impl<P> Reducer<P> for ProductConsumer<P>
where
    P: Send + Product,
{
    #[inline]
    fn reduce(self, left: P, right: P) -> P {
        mul(left, right)
    }
}

struct ProductFolder<P> {
    product: P,
}

impl<P, T> Folder<T> for ProductFolder<P>
where
    P: Product<T> + Product<P>,
{
    type Result = P;

    #[inline]
    fn consume(self, item: T) -> Self {
        ProductFolder {
            product: mul(self.product, iter::once(item).product()),
        }
    }

    #[inline]
    fn consume_iter<I>(self, iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        ProductFolder {
            product: mul(self.product, iter.into_iter().product()),
        }
    }

    fn complete(self) -> P {
        self.product
    }

    fn full(&self) -> bool {
        false
    }
}
