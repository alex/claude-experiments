//! Parallel iterators over the standard collections.
//!
//! `VecDeque` iterates directly over its two contiguous slices (zero
//! copies). The node-based / hashed collections (`HashMap`, `HashSet`,
//! `BTreeMap`, `BTreeSet`, `LinkedList`, `BinaryHeap`) don't expose
//! splittable internal structure, so (as in rayon) their parallel
//! iterators collect the (references to) items into a `Vec` first and
//! iterate that in parallel -- O(n) setup, worth it whenever per-item
//! work dominates.

use crate::iter::{Chain, IntoParallelIterator, ParallelIterator};
use crate::{slice, vec};
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, LinkedList, VecDeque};
use std::hash::{BuildHasher, Hash};

// //////////////////////////////////////////////////////////////////////
// VecDeque: true zero-copy slice-based iteration.

impl<'a, T: Sync> IntoParallelIterator for &'a VecDeque<T> {
    type Item = &'a T;
    type Iter = Chain<slice::Iter<'a, T>, slice::Iter<'a, T>>;

    fn into_par_iter(self) -> Self::Iter {
        let (a, b) = self.as_slices();
        a.into_par_iter().chain(b)
    }
}

impl<'a, T: Send> IntoParallelIterator for &'a mut VecDeque<T> {
    type Item = &'a mut T;
    type Iter = Chain<slice::IterMut<'a, T>, slice::IterMut<'a, T>>;

    fn into_par_iter(self) -> Self::Iter {
        let (a, b) = self.as_mut_slices();
        a.into_par_iter().chain(b)
    }
}

impl<T: Send> IntoParallelIterator for VecDeque<T> {
    type Item = T;
    type Iter = vec::IntoIter<T>;

    fn into_par_iter(self) -> Self::Iter {
        // O(1)-ish: rotates in place, no per-item copies beyond the
        // possible internal rotation.
        Vec::from(self).into_par_iter()
    }
}

// //////////////////////////////////////////////////////////////////////
// BinaryHeap: Vec conversion is free.

impl<T: Send> IntoParallelIterator for BinaryHeap<T> {
    type Item = T;
    type Iter = vec::IntoIter<T>;

    fn into_par_iter(self) -> Self::Iter {
        self.into_vec().into_par_iter()
    }
}

impl<'a, T: Sync> IntoParallelIterator for &'a BinaryHeap<T> {
    type Item = &'a T;
    type Iter = vec::IntoIter<&'a T>;

    fn into_par_iter(self) -> Self::Iter {
        self.iter().collect::<Vec<_>>().into_par_iter()
    }
}

// //////////////////////////////////////////////////////////////////////
// Buffering delegation for the node-based collections.

macro_rules! delegate_via_vec {
    // by-value
    ($t:ty, $item:ty, [$($generics:tt)*], [$($bounds:tt)*]) => {
        impl<$($generics)*> IntoParallelIterator for $t
        where
            $($bounds)*
        {
            type Item = $item;
            type Iter = vec::IntoIter<$item>;

            fn into_par_iter(self) -> Self::Iter {
                self.into_iter().collect::<Vec<_>>().into_par_iter()
            }
        }
    };
}

// HashMap
delegate_via_vec!(HashMap<K, V, S>, (K, V), [K, V, S], [K: Hash + Eq + Send, V: Send, S: BuildHasher]);
delegate_via_vec!(&'a HashMap<K, V, S>, (&'a K, &'a V), ['a, K, V, S], [K: Hash + Eq + Sync, V: Sync, S: BuildHasher]);
delegate_via_vec!(&'a mut HashMap<K, V, S>, (&'a K, &'a mut V), ['a, K, V, S], [K: Hash + Eq + Sync, V: Send, S: BuildHasher]);

// HashSet
delegate_via_vec!(HashSet<T, S>, T, [T, S], [T: Hash + Eq + Send, S: BuildHasher]);
delegate_via_vec!(&'a HashSet<T, S>, &'a T, ['a, T, S], [T: Hash + Eq + Sync, S: BuildHasher]);

// BTreeMap
delegate_via_vec!(BTreeMap<K, V>, (K, V), [K, V], [K: Ord + Send, V: Send]);
delegate_via_vec!(&'a BTreeMap<K, V>, (&'a K, &'a V), ['a, K, V], [K: Ord + Sync, V: Sync]);
delegate_via_vec!(&'a mut BTreeMap<K, V>, (&'a K, &'a mut V), ['a, K, V], [K: Ord + Sync, V: Send]);

// BTreeSet
delegate_via_vec!(BTreeSet<T>, T, [T], [T: Ord + Send]);
delegate_via_vec!(&'a BTreeSet<T>, &'a T, ['a, T], [T: Ord + Sync]);

// LinkedList
delegate_via_vec!(LinkedList<T>, T, [T], [T: Send]);
delegate_via_vec!(&'a LinkedList<T>, &'a T, ['a, T], [T: Sync]);
delegate_via_vec!(&'a mut LinkedList<T>, &'a mut T, ['a, T], [T: Send]);
