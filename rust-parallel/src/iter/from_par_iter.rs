//! `FromParallelIterator` / `ParallelExtend` implementations for the
//! standard collections: what `collect()` and `par_extend()` can target.
//!
//! Strategy (same as rayon): fold items into per-leaf `Vec`s in
//! parallel, splice the resulting list into the target sequentially.
//! `Vec` itself has a faster fully-parallel in-place path (see
//! `collect.rs`).

use super::collect::ListVecConsumer;
use super::{FromParallelIterator, IntoParallelIterator, ParallelExtend, ParallelIterator};
use std::collections::LinkedList;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque};
use std::hash::{BuildHasher, Hash};

/// Drives `par_iter` into per-leaf vectors.
fn collect_vec_list<I>(par_iter: I) -> LinkedList<Vec<I::Item>>
where
    I: ParallelIterator,
{
    par_iter.drive_unindexed(ListVecConsumer)
}

fn combined_len<T>(list: &LinkedList<Vec<T>>) -> usize {
    list.iter().map(Vec::len).sum()
}

macro_rules! extend_via_list {
    ($t:ty, [$($generics:tt)*], [$($bounds:tt)*], $reserve:expr) => {
        impl<$($generics)*> ParallelExtend<T> for $t
        where
            $($bounds)*
        {
            fn par_extend<I>(&mut self, par_iter: I)
            where
                I: IntoParallelIterator<Item = T>,
            {
                let list = collect_vec_list(par_iter.into_par_iter());
                #[allow(clippy::redundant_closure_call)]
                ($reserve)(self, combined_len(&list));
                for vec in list {
                    self.extend(vec);
                }
            }
        }

        impl<$($generics)*> FromParallelIterator<T> for $t
        where
            $($bounds)*
        {
            fn from_par_iter<I>(par_iter: I) -> Self
            where
                I: IntoParallelIterator<Item = T>,
            {
                let mut collection = <$t>::default();
                collection.par_extend(par_iter);
                collection
            }
        }
    };
}

extend_via_list!(VecDeque<T>, [T], [T: Send], |c: &mut VecDeque<T>, n| c.reserve(n));
extend_via_list!(BinaryHeap<T>, [T], [T: Ord + Send], |c: &mut BinaryHeap<T>, n| c.reserve(n));
extend_via_list!(HashSet<T, S>, [T, S], [T: Hash + Eq + Send, S: BuildHasher + Default + Send], |c: &mut HashSet<T, S>, n| c.reserve(n));
extend_via_list!(BTreeSet<T>, [T], [T: Ord + Send], |_c: &mut BTreeSet<T>, _n| ());
extend_via_list!(LinkedList<T>, [T], [T: Send], |_c: &mut LinkedList<T>, _n| ());

// Maps need the (K, V) tuple item type spelled out.

macro_rules! extend_map_via_list {
    ($t:ty, [$($generics:tt)*], [$($bounds:tt)*], $reserve:expr) => {
        impl<$($generics)*> ParallelExtend<(K, V)> for $t
        where
            $($bounds)*
        {
            fn par_extend<I>(&mut self, par_iter: I)
            where
                I: IntoParallelIterator<Item = (K, V)>,
            {
                let list = collect_vec_list(par_iter.into_par_iter());
                #[allow(clippy::redundant_closure_call)]
                ($reserve)(self, combined_len(&list));
                for vec in list {
                    self.extend(vec);
                }
            }
        }

        impl<$($generics)*> FromParallelIterator<(K, V)> for $t
        where
            $($bounds)*
        {
            fn from_par_iter<I>(par_iter: I) -> Self
            where
                I: IntoParallelIterator<Item = (K, V)>,
            {
                let mut collection = <$t>::default();
                collection.par_extend(par_iter);
                collection
            }
        }
    };
}

extend_map_via_list!(HashMap<K, V, S>, [K, V, S], [K: Hash + Eq + Send, V: Send, S: BuildHasher + Default + Send], |c: &mut HashMap<K, V, S>, n| c.reserve(n));
extend_map_via_list!(BTreeMap<K, V>, [K, V], [K: Ord + Send, V: Send], |_c: &mut BTreeMap<K, V>, _n| ());

// //////////////////////////////////////////////////////////////////////
// Strings

impl ParallelExtend<char> for String {
    fn par_extend<I>(&mut self, par_iter: I)
    where
        I: IntoParallelIterator<Item = char>,
    {
        // Fold into per-leaf strings, then concatenate.
        let list = par_iter
            .into_par_iter()
            .fold(String::new, |mut s, c| {
                s.push(c);
                s
            })
            .drive_unindexed(ListVecConsumer);
        self.reserve(list.iter().flatten().map(String::len).sum());
        for vec in list {
            for s in vec {
                self.push_str(&s);
            }
        }
    }
}

impl FromParallelIterator<char> for String {
    fn from_par_iter<I>(par_iter: I) -> Self
    where
        I: IntoParallelIterator<Item = char>,
    {
        let mut s = String::new();
        s.par_extend(par_iter);
        s
    }
}

macro_rules! extend_string_from_str {
    ($item:ty) => {
        impl<'a> ParallelExtend<$item> for String {
            fn par_extend<I>(&mut self, par_iter: I)
            where
                I: IntoParallelIterator<Item = $item>,
            {
                let list = collect_vec_list(par_iter.into_par_iter());
                self.reserve(
                    list.iter()
                        .flatten()
                        .map(|s| AsRef::<str>::as_ref(s).len())
                        .sum(),
                );
                for vec in list {
                    for s in vec {
                        self.push_str(s.as_ref());
                    }
                }
            }
        }

        impl<'a> FromParallelIterator<$item> for String {
            fn from_par_iter<I>(par_iter: I) -> Self
            where
                I: IntoParallelIterator<Item = $item>,
            {
                let mut s = String::new();
                s.par_extend(par_iter);
                s
            }
        }
    };
}

extend_string_from_str!(&'a str);
extend_string_from_str!(String);

// //////////////////////////////////////////////////////////////////////
// Unit: useful for `collect::<()>()` on iterators of ()

impl FromParallelIterator<()> for () {
    fn from_par_iter<I>(par_iter: I)
    where
        I: IntoParallelIterator<Item = ()>,
    {
        par_iter.into_par_iter().drive_unindexed(super::noop::NoopConsumer)
    }
}
