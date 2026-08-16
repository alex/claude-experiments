//! Integration tests for filament's adapters, sources, collect targets,
//! strings, scope/spawn, and parallel sorts, validated against their
//! sequential std equivalents.
//!
//! Execution order across threads is unspecified, so wherever the result
//! order is not guaranteed we compare against the sequential result as a
//! sorted multiset. `find_any` / `position_any` return *any* match, so we
//! only verify the returned item/index actually matches.

use filament::prelude::*;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, LinkedList, VecDeque};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

/// Tiny deterministic LCG so we need no external crates.
fn lcg(seed: &mut u64) -> u64 {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *seed >> 33
}

fn lcg_vec(n: usize, seed: u64) -> Vec<u64> {
    let mut s = seed;
    (0..n).map(|_| lcg(&mut s)).collect()
}

fn sorted<T: Ord>(mut v: Vec<T>) -> Vec<T> {
    v.sort();
    v
}

// ////////////////////////////////////////////////////////////////////////
// Basic adapters

#[test]
fn map_collect_indexed_preserves_order() {
    let v: Vec<i64> = (0..10_000).collect();
    let par: Vec<i64> = v.par_iter().map(|&x| x * 2 - 1).collect();
    let seq: Vec<i64> = v.iter().map(|&x| x * 2 - 1).collect();
    assert_eq!(par, seq);
}

#[test]
fn filter_collect_unindexed_matches_sequential() {
    // `filter` destroys the exact-length property, so this exercises the
    // unindexed (per-leaf buffers) collect path.
    let v: Vec<u64> = lcg_vec(20_000, 1);
    let par: Vec<u64> = v.par_iter().copied().filter(|x| x % 3 == 0).collect();
    let seq: Vec<u64> = v.iter().copied().filter(|x| x % 3 == 0).collect();
    assert_eq!(par, seq);
}

#[test]
fn filter_map_collect_matches_sequential() {
    let v: Vec<u64> = lcg_vec(20_000, 2);
    let f = |x: u64| if x % 2 == 0 { Some(x / 2) } else { None };
    let par: Vec<u64> = v.par_iter().filter_map(|&x| f(x)).collect();
    let seq: Vec<u64> = v.iter().filter_map(|&x| f(x)).collect();
    assert_eq!(par, seq);
}

#[test]
fn flat_map_inner_vec_matches_sequential() {
    let par: Vec<u32> = (0..1000u32)
        .into_par_iter()
        .flat_map(|x| vec![x, x * 10, x * 100])
        .collect();
    let seq: Vec<u32> = (0..1000u32).flat_map(|x| vec![x, x * 10, x * 100]).collect();
    assert_eq!(par, seq);
}

#[test]
fn flat_map_inner_range_matches_sequential() {
    let par: u64 = (0..200u64).into_par_iter().flat_map(|x| 0..x).sum();
    let seq: u64 = (0..200u64).flat_map(|x| 0..x).sum();
    assert_eq!(par, seq);
}

#[test]
fn flat_map_iter_matches_sequential() {
    let par: Vec<u32> = (0..1000u32)
        .into_par_iter()
        .flat_map_iter(|x| (0..x % 5).map(move |y| x + y))
        .collect();
    let seq: Vec<u32> = (0..1000u32)
        .flat_map(|x| (0..x % 5).map(move |y| x + y))
        .collect();
    assert_eq!(par, seq);
}

#[test]
fn flatten_and_flatten_iter_match_sequential() {
    let nested: Vec<Vec<i32>> = (0..300)
        .map(|i| (0..i % 7).map(|j| i * 100 + j).collect())
        .collect();
    let seq: Vec<i32> = nested.clone().into_iter().flatten().collect();

    let par: Vec<i32> = nested.clone().into_par_iter().flatten().collect();
    assert_eq!(par, seq);

    let par2: Vec<i32> = nested.into_par_iter().flatten_iter().collect();
    assert_eq!(par2, seq);
}

#[test]
fn inspect_visits_every_item() {
    let count = AtomicUsize::new(0);
    let sum: u64 = (0..10_000u64)
        .into_par_iter()
        .inspect(|_| {
            count.fetch_add(1, Ordering::Relaxed);
        })
        .sum();
    assert_eq!(count.load(Ordering::Relaxed), 10_000);
    assert_eq!(sum, (0..10_000u64).sum::<u64>());
}

#[test]
fn copied_and_cloned() {
    let v: Vec<u32> = (0..5000).collect();
    let par_copied: Vec<u32> = v.par_iter().copied().collect();
    assert_eq!(par_copied, v);

    let words: Vec<String> = (0..500).map(|i| format!("w{i}")).collect();
    let par_cloned: Vec<String> = words.par_iter().cloned().collect();
    assert_eq!(par_cloned, words);
}

#[test]
fn chain_matches_sequential() {
    let a: Vec<i32> = (0..1000).collect();
    let b: Vec<i32> = (5000..5500).collect();
    let par: Vec<i32> = a.par_iter().chain(b.par_iter()).copied().collect();
    let seq: Vec<i32> = a.iter().chain(b.iter()).copied().collect();
    assert_eq!(par, seq);
    assert_eq!(a.par_iter().chain(b.par_iter()).count(), 1500);
}

#[test]
fn chain_empty_and_nonempty() {
    let empty: Vec<i32> = vec![];
    let full: Vec<i32> = (0..100).collect();
    let par: Vec<i32> = empty.par_iter().chain(full.par_iter()).copied().collect();
    assert_eq!(par, full);
    let par2: Vec<i32> = full.par_iter().chain(empty.par_iter()).copied().collect();
    assert_eq!(par2, full);
    let par3: Vec<i32> = empty.par_iter().chain(empty.par_iter()).copied().collect();
    assert!(par3.is_empty());
}

// ////////////////////////////////////////////////////////////////////////
// fold / reduce

#[test]
fn fold_then_sum_matches_sequential_fold() {
    let v: Vec<u64> = lcg_vec(50_000, 3).iter().map(|x| x % 1000).collect();
    let par: u64 = v.par_iter().fold(|| 0u64, |acc, &x| acc + x).sum();
    let seq: u64 = v.iter().fold(0u64, |acc, &x| acc + x);
    assert_eq!(par, seq);
}

#[test]
fn fold_then_reduce_matches_sequential() {
    let par: u64 = (0..100_000u64)
        .into_par_iter()
        .fold(|| 0u64, |acc, x| acc + x % 17)
        .reduce(|| 0, |a, b| a + b);
    let seq: u64 = (0..100_000u64).map(|x| x % 17).sum();
    assert_eq!(par, seq);
}

#[test]
fn fold_with_matches_sequential() {
    let v: Vec<u64> = (0..10_000).collect();
    let par: u64 = v.par_iter().fold_with(0u64, |acc, &x| acc + x * 3).sum();
    let seq: u64 = v.iter().map(|&x| x * 3).sum();
    assert_eq!(par, seq);
}

#[test]
fn reduce_with_identity_matches() {
    let v: Vec<u64> = lcg_vec(10_000, 4).iter().map(|x| x % 100).collect();
    let par = v.par_iter().copied().reduce(|| 0, |a, b| a + b);
    assert_eq!(par, v.iter().sum::<u64>());
    // reduce on an empty iterator yields the identity.
    let empty: Vec<u64> = vec![];
    assert_eq!(empty.par_iter().copied().reduce(|| 42, |a, b| a + b), 42);
}

#[test]
fn reduce_with_nonempty_and_empty() {
    let v: Vec<u64> = (1..=1000).collect();
    let par = v.par_iter().copied().reduce_with(|a, b| a + b);
    assert_eq!(par, Some(500_500));

    let empty: Vec<u64> = vec![];
    assert_eq!(empty.par_iter().copied().reduce_with(|a, b| a + b), None);
}

#[test]
fn sum_product_count() {
    let v: Vec<u64> = (1..=15).collect();
    assert_eq!(v.par_iter().copied().sum::<u64>(), 120);
    assert_eq!(v.par_iter().copied().product::<u64>(), 1_307_674_368_000);
    assert_eq!(v.par_iter().count(), 15);

    let empty: Vec<u64> = vec![];
    assert_eq!(empty.par_iter().copied().sum::<u64>(), 0);
    assert_eq!(empty.par_iter().copied().product::<u64>(), 1);
    assert_eq!(empty.par_iter().count(), 0);
}

// ////////////////////////////////////////////////////////////////////////
// min / max family

#[test]
fn min_max_match_sequential() {
    let v: Vec<u64> = lcg_vec(30_000, 5);
    assert_eq!(v.par_iter().min(), v.iter().min());
    assert_eq!(v.par_iter().max(), v.iter().max());

    // Single element.
    let one = vec![7u64];
    assert_eq!(one.par_iter().copied().min(), Some(7));
    assert_eq!(one.par_iter().copied().max(), Some(7));
}

#[test]
fn min_max_empty_is_none() {
    let empty: Vec<u64> = vec![];
    assert_eq!(empty.par_iter().min(), None);
    assert_eq!(empty.par_iter().max(), None);
    assert_eq!(empty.par_iter().min_by_key(|&&x| x), None);
    assert_eq!(empty.par_iter().max_by(|a, b| a.cmp(b)), None);
}

#[test]
fn min_by_max_by_comparator() {
    // Distinct absolute values so the answer is unique regardless of
    // reduction order.
    let v: Vec<i64> = (1..=999)
        .map(|i| if i % 2 == 0 { i } else { -i })
        .collect();
    let par_min = v.par_iter().min_by(|a, b| a.abs().cmp(&b.abs()));
    let seq_min = v.iter().min_by(|a, b| a.abs().cmp(&b.abs()));
    assert_eq!(par_min, seq_min);

    let par_max = v.par_iter().max_by(|a, b| a.abs().cmp(&b.abs()));
    let seq_max = v.iter().max_by(|a, b| a.abs().cmp(&b.abs()));
    assert_eq!(par_max, seq_max);
}

#[test]
fn min_by_key_max_by_key() {
    // 7 is invertible mod 1000, so all keys are distinct: unique answers.
    let v: Vec<u64> = (0..1000).collect();
    let key = |x: u64| (x * 7) % 1000;
    let par_min = v.par_iter().min_by_key(|&&x| key(x)).copied();
    let seq_min = v.iter().min_by_key(|&&x| key(x)).copied();
    assert_eq!(par_min, seq_min);

    let par_max = v.par_iter().max_by_key(|&&x| key(x)).copied();
    let seq_max = v.iter().max_by_key(|&&x| key(x)).copied();
    assert_eq!(par_max, seq_max);
}

// ////////////////////////////////////////////////////////////////////////
// find / any / all / position

#[test]
fn find_any_returns_a_match() {
    let v: Vec<u64> = (0..100_000).collect();
    let found = v.par_iter().find_any(|&&x| x % 9999 == 0 && x > 0);
    let x = *found.expect("a match exists");
    assert!(x % 9999 == 0 && x > 0);

    assert_eq!(v.par_iter().find_any(|&&x| x > 1_000_000), None);
}

#[test]
fn any_all_basics() {
    let v: Vec<u64> = (0..10_000).collect();
    assert!(v.par_iter().any(|&x| x == 9_999));
    assert!(!v.par_iter().any(|&x| x >= 10_000));
    assert!(v.par_iter().all(|&x| x < 10_000));
    assert!(!v.par_iter().all(|&x| x != 5_000));

    let empty: Vec<u64> = vec![];
    assert!(!empty.par_iter().any(|_| true));
    assert!(empty.par_iter().all(|_| false));
}

#[test]
fn any_all_early_exit_on_large_range() {
    // These must short-circuit; on 10M items even a full scan finishes,
    // but early exit is what keeps them near-instant.
    assert!((0..10_000_000u64).into_par_iter().any(|x| x == 12_345));
    assert!(!(0..10_000_000u64).into_par_iter().all(|x| x != 12_345));
}

#[test]
fn position_any_returns_valid_index() {
    let v: Vec<u64> = (0..50_000).map(|i| i * 2).collect();
    // Unique match.
    let pos = v.par_iter().position_any(|&x| x == 700);
    assert_eq!(pos, Some(350));
    // Many matches: any valid index is fine, but it must actually match.
    let pos = v
        .par_iter()
        .position_any(|&x| x % 14 == 0 && x > 0)
        .expect("matches exist");
    assert!(v[pos] % 14 == 0 && v[pos] > 0);
    // No match.
    assert_eq!(v.par_iter().position_any(|&x| x % 2 == 1), None);
}

#[test]
fn for_each_touches_each_item_once() {
    let n = 25_000u64;
    let count = AtomicUsize::new(0);
    let total = AtomicU64::new(0);
    (0..n).into_par_iter().for_each(|i| {
        count.fetch_add(1, Ordering::Relaxed);
        total.fetch_add(i, Ordering::Relaxed);
    });
    assert_eq!(count.load(Ordering::Relaxed), n as usize);
    assert_eq!(total.load(Ordering::Relaxed), n * (n - 1) / 2);
}

// ////////////////////////////////////////////////////////////////////////
// Indexed adapters

#[test]
fn len_reports_exact_length() {
    let v: Vec<u8> = vec![0; 1234];
    assert_eq!(v.par_iter().len(), 1234);
    assert_eq!((0..77u64).into_par_iter().len(), 77);
    assert_eq!(v.par_iter().skip(1000).len(), 234);
    assert_eq!(v.par_iter().take(34).len(), 34);
    assert_eq!(v.par_iter().rev().len(), 1234);
}

#[test]
fn zip_stops_at_shorter_side() {
    let a: Vec<u64> = (0..100).collect();
    let b: Vec<u64> = (0..37).map(|x| x * 10).collect();
    let par: Vec<(u64, u64)> = a
        .par_iter()
        .copied()
        .zip(b.par_iter().copied())
        .collect();
    let seq: Vec<(u64, u64)> = a.iter().copied().zip(b.iter().copied()).collect();
    assert_eq!(par, seq);
    assert_eq!(par.len(), 37);

    // Symmetric: shorter on the left.
    let par2: Vec<(u64, u64)> = b
        .par_iter()
        .copied()
        .zip(a.par_iter().copied())
        .collect();
    assert_eq!(par2.len(), 37);
}

#[test]
fn zip_eq_equal_lengths_ok() {
    let a: Vec<u64> = (0..1000).collect();
    let par: Vec<(u64, u64)> = a
        .par_iter()
        .copied()
        .zip_eq((1000..2000u64).into_par_iter())
        .collect();
    let seq: Vec<(u64, u64)> = a.iter().copied().zip(1000..2000u64).collect();
    assert_eq!(par, seq);
}

#[test]
fn zip_eq_mismatched_lengths_panics() {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let a: Vec<u64> = (0..10).collect();
        let z = a.par_iter().zip_eq((0..11u64).into_par_iter());
        drop(z);
    }));
    assert!(result.is_err(), "zip_eq must panic on length mismatch");
}

#[test]
fn enumerate_indices_complete_and_unique() {
    let v: Vec<u64> = (0..10_000).map(|i| i * 3).collect();
    let mut pairs: Vec<(usize, u64)> = v.par_iter().copied().enumerate().collect();
    pairs.sort();
    assert_eq!(pairs.len(), v.len());
    for (i, (idx, val)) in pairs.iter().enumerate() {
        assert_eq!(*idx, i, "indices must be exactly 0..len with no gaps");
        assert_eq!(*val, v[i], "index must pair with the right element");
    }
}

#[test]
fn rev_matches_sequential_and_roundtrips() {
    let v: Vec<i32> = (0..5000).collect();
    let par: Vec<i32> = v.par_iter().copied().rev().collect();
    let seq: Vec<i32> = v.iter().copied().rev().collect();
    assert_eq!(par, seq);

    let roundtrip: Vec<i32> = v.par_iter().copied().rev().rev().collect();
    assert_eq!(roundtrip, v);
}

#[test]
fn skip_take_variants() {
    let v: Vec<u32> = (0..1000).collect();

    let par: Vec<u32> = v.par_iter().copied().skip(100).collect();
    assert_eq!(par, (100..1000).collect::<Vec<u32>>());

    let par: Vec<u32> = v.par_iter().copied().take(100).collect();
    assert_eq!(par, (0..100).collect::<Vec<u32>>());

    // skip more than len -> empty
    assert!(v.par_iter().copied().skip(5000).collect::<Vec<u32>>().is_empty());
    // take(0) -> empty
    assert!(v.par_iter().copied().take(0).collect::<Vec<u32>>().is_empty());
    // take more than len -> everything
    assert_eq!(v.par_iter().copied().take(9999).collect::<Vec<u32>>(), v);
    // skip(0) -> everything
    assert_eq!(v.par_iter().copied().skip(0).collect::<Vec<u32>>(), v);
    // combined
    let par: Vec<u32> = v.par_iter().copied().skip(200).take(50).collect();
    assert_eq!(par, (200..250).collect::<Vec<u32>>());
}

#[test]
fn with_min_len_max_len_do_not_change_results() {
    let seq: u64 = (0..100_000u64).sum();
    let a: u64 = (0..100_000u64).into_par_iter().with_min_len(10_000).sum();
    let b: u64 = (0..100_000u64).into_par_iter().with_max_len(64).sum();
    let c: Vec<u64> = (0..1000u64).into_par_iter().with_max_len(1).collect();
    assert_eq!(a, seq);
    assert_eq!(b, seq);
    assert_eq!(c, (0..1000u64).collect::<Vec<u64>>());
    let d: Vec<u64> = (0..1000u64).into_par_iter().with_min_len(100_000).collect();
    assert_eq!(d, (0..1000u64).collect::<Vec<u64>>());
}

#[test]
fn collect_into_vec_replaces_contents() {
    let mut target = vec![9u64; 5]; // stale contents must be discarded
    (0..1000u64).into_par_iter().map(|x| x + 1).collect_into_vec(&mut target);
    assert_eq!(target, (1..=1000u64).collect::<Vec<u64>>());

    // Empty source leaves an empty vec.
    let mut target2 = vec![1u32, 2, 3];
    Vec::<u32>::new().into_par_iter().collect_into_vec(&mut target2);
    assert!(target2.is_empty());
}

// ////////////////////////////////////////////////////////////////////////
// Sources

#[test]
fn vec_sources_by_value_ref_and_mut() {
    let v: Vec<u64> = (0..10_000).collect();
    let seq_sum: u64 = v.iter().sum();

    // &Vec
    assert_eq!(v.par_iter().sum::<u64>(), seq_sum);
    assert_eq!((&v).into_par_iter().copied().sum::<u64>(), seq_sum);

    // &mut Vec
    let mut m = v.clone();
    m.par_iter_mut().for_each(|x| *x *= 2);
    assert_eq!(m.iter().sum::<u64>(), seq_sum * 2);

    // Vec by value
    let owned_sum: u64 = v.clone().into_par_iter().sum();
    assert_eq!(owned_sum, seq_sum);

    // By value with non-Copy items (checks ownership transfer).
    let strings: Vec<String> = (0..100).map(|i| i.to_string()).collect();
    let lens: usize = strings.into_par_iter().map(|s| s.len()).sum();
    let seq_lens: usize = (0..100).map(|i: i32| i.to_string().len()).sum();
    assert_eq!(lens, seq_lens);
}

#[test]
fn slice_sources_ref_and_mut() {
    let v: Vec<i64> = (0..5000).collect();
    let s: &[i64] = &v;
    assert_eq!(s.into_par_iter().sum::<i64>(), v.iter().sum::<i64>());
    assert_eq!(s.par_iter().max(), Some(&4999));

    let mut m: Vec<i64> = (0..5000).collect();
    let ms: &mut [i64] = &mut m;
    ms.into_par_iter().for_each(|x| *x += 1);
    assert_eq!(m, (1..=5000).collect::<Vec<i64>>());
}

#[test]
fn range_sources_wide_types() {
    let par: u64 = (0..2_000_000u64).into_par_iter().sum();
    assert_eq!(par, (0..2_000_000u64).sum::<u64>());

    let par: i64 = (-1_000_000..1_000_000i64).into_par_iter().sum();
    assert_eq!(par, 2_000_000 * -1 / 2); // sum of -1M..1M = -1_000_000
    assert_eq!(par, (-1_000_000..1_000_000i64).sum::<i64>());

    assert_eq!((0..0u32).into_par_iter().count(), 0);
    assert_eq!((5..6i8).into_par_iter().count(), 1);
}

#[test]
fn range_inclusive_sources() {
    assert_eq!((1..=100u32).into_par_iter().sum::<u32>(), 5050);
    // Full u8 domain: must terminate without overflow.
    assert_eq!((0..=255u8).into_par_iter().map(|b| b as u32).sum::<u32>(), 32_640);
    assert_eq!((0..=255u8).into_par_iter().count(), 256);
    assert_eq!((7..=7i64).into_par_iter().collect::<Vec<i64>>(), vec![7]);
    #[allow(clippy::reversed_empty_ranges)]
    {
        assert_eq!((5..=4u32).into_par_iter().count(), 0);
    }
}

#[test]
fn option_sources() {
    let some = Some(41u64);
    let none: Option<u64> = None;

    assert_eq!(some.into_par_iter().map(|x| x + 1).sum::<u64>(), 42);
    assert_eq!(none.into_par_iter().count(), 0);

    let some_ref = Some(10u64);
    assert_eq!(some_ref.par_iter().copied().collect::<Vec<u64>>(), vec![10]);
    assert_eq!((&none).into_par_iter().count(), 0);

    let mut some_mut = Some(1u64);
    some_mut.par_iter_mut().for_each(|x| *x += 99);
    assert_eq!(some_mut, Some(100));
}

#[test]
fn result_sources() {
    let ok: Result<u64, String> = Ok(5);
    let err: Result<u64, String> = Err("nope".to_string());

    assert_eq!(ok.clone().into_par_iter().sum::<u64>(), 5);
    assert_eq!(err.clone().into_par_iter().count(), 0);

    assert_eq!(ok.par_iter().copied().collect::<Vec<u64>>(), vec![5]);
    assert_eq!(err.par_iter().count(), 0);

    let mut ok_mut: Result<u64, String> = Ok(1);
    ok_mut.par_iter_mut().for_each(|x| *x = 77);
    assert_eq!(ok_mut, Ok(77));
    let mut err_mut: Result<u64, String> = Err("e".into());
    err_mut.par_iter_mut().for_each(|x| *x = 77);
    assert!(err_mut.is_err());
}

#[test]
fn array_sources() {
    let arr: [u64; 6] = [1, 2, 3, 4, 5, 6];

    // By value.
    assert_eq!(arr.into_par_iter().sum::<u64>(), 21);
    let strings: [String; 3] = ["a".into(), "bb".into(), "ccc".into()];
    assert_eq!(strings.into_par_iter().map(|s| s.len()).sum::<usize>(), 6);

    // By reference.
    assert_eq!(arr.par_iter().copied().max(), Some(6));
    assert_eq!((&arr).into_par_iter().copied().collect::<Vec<u64>>(), arr.to_vec());

    // By mutable reference.
    let mut m = [1u64, 2, 3, 4];
    m.par_iter_mut().for_each(|x| *x *= 10);
    assert_eq!(m, [10, 20, 30, 40]);

    // Empty array.
    let empty: [u64; 0] = [];
    assert_eq!(empty.into_par_iter().count(), 0);
}

#[test]
fn vecdeque_sources() {
    // Rotate so as_slices() returns two non-empty halves.
    let mut dq: VecDeque<u64> = (0..1000).collect();
    dq.rotate_left(337);
    let seq: Vec<u64> = dq.iter().copied().collect();

    // &VecDeque (a Chain of the two slices -- still indexed).
    let par: Vec<u64> = dq.par_iter().copied().collect();
    assert_eq!(par, seq);
    assert_eq!(dq.par_iter().len(), 1000);
    let pairs: Vec<(usize, u64)> = dq.par_iter().copied().enumerate().collect();
    let seq_pairs: Vec<(usize, u64)> = seq.iter().copied().enumerate().collect();
    assert_eq!(pairs, seq_pairs);

    // &mut VecDeque
    let mut dq2 = dq.clone();
    dq2.par_iter_mut().for_each(|x| *x += 1);
    assert_eq!(
        dq2.iter().copied().collect::<Vec<u64>>(),
        seq.iter().map(|x| x + 1).collect::<Vec<u64>>()
    );

    // By value.
    let par_sum: u64 = dq.clone().into_par_iter().sum();
    assert_eq!(par_sum, seq.iter().sum::<u64>());

    // Empty deque.
    let empty: VecDeque<u64> = VecDeque::new();
    assert_eq!(empty.par_iter().count(), 0);
}

#[test]
fn binary_heap_sources() {
    let heap: BinaryHeap<u64> = lcg_vec(2000, 6).into_iter().map(|x| x % 500).collect();
    let expected = sorted(heap.iter().copied().collect::<Vec<u64>>());

    // &BinaryHeap
    let by_ref = sorted(heap.par_iter().copied().collect::<Vec<u64>>());
    assert_eq!(by_ref, expected);
    assert_eq!(heap.par_iter().copied().max(), heap.iter().copied().max());

    // By value.
    let by_val = sorted(heap.into_par_iter().collect::<Vec<u64>>());
    assert_eq!(by_val, expected);
}

#[test]
fn hashmap_sources() {
    let map: HashMap<u32, u64> = (0..1000).map(|i| (i, (i as u64) * 7)).collect();
    let expected: Vec<(u32, u64)> = sorted(map.iter().map(|(&k, &v)| (k, v)).collect());

    // &HashMap
    let by_ref: Vec<(u32, u64)> = sorted(map.par_iter().map(|(&k, &v)| (k, v)).collect());
    assert_eq!(by_ref, expected);

    // &mut HashMap
    let mut map2 = map.clone();
    map2.par_iter_mut().for_each(|(&k, v)| *v += k as u64);
    for (k, v) in &map2 {
        assert_eq!(*v, (*k as u64) * 8);
    }

    // By value.
    let by_val: Vec<(u32, u64)> = sorted(map.into_par_iter().collect());
    assert_eq!(by_val, expected);
}

#[test]
fn hashset_sources() {
    let set: HashSet<u64> = (0..1000).map(|i| i * 3).collect();
    let expected = sorted(set.iter().copied().collect::<Vec<u64>>());

    let by_ref = sorted(set.par_iter().copied().collect::<Vec<u64>>());
    assert_eq!(by_ref, expected);
    assert_eq!(set.par_iter().count(), 1000);

    let by_val = sorted(set.into_par_iter().collect::<Vec<u64>>());
    assert_eq!(by_val, expected);
}

#[test]
fn btreemap_sources() {
    let map: BTreeMap<u32, String> = (0..500).map(|i| (i, format!("v{i}"))).collect();
    let expected: Vec<(u32, String)> =
        map.iter().map(|(&k, v)| (k, v.clone())).collect();

    // &BTreeMap
    let by_ref: Vec<(u32, String)> =
        sorted(map.par_iter().map(|(&k, v)| (k, v.clone())).collect());
    assert_eq!(by_ref, expected);

    // &mut BTreeMap
    let mut map2 = map.clone();
    map2.par_iter_mut().for_each(|(_k, v)| v.push('!'));
    assert!(map2.values().all(|v| v.ends_with('!')));

    // By value.
    let by_val: Vec<(u32, String)> = sorted(map.into_par_iter().collect());
    assert_eq!(by_val, expected);
}

#[test]
fn btreeset_sources() {
    let set: BTreeSet<i64> = (-250..250).collect();
    let expected: Vec<i64> = set.iter().copied().collect();

    let by_ref = sorted(set.par_iter().copied().collect::<Vec<i64>>());
    assert_eq!(by_ref, expected);
    assert_eq!(set.par_iter().copied().min(), Some(-250));

    let by_val = sorted(set.into_par_iter().collect::<Vec<i64>>());
    assert_eq!(by_val, expected);
}

#[test]
fn linked_list_sources() {
    let list: LinkedList<u64> = (0..500).collect();
    let expected: Vec<u64> = (0..500).collect();

    // &LinkedList
    let by_ref = sorted(list.par_iter().copied().collect::<Vec<u64>>());
    assert_eq!(by_ref, expected);

    // &mut LinkedList
    let mut list2 = list.clone();
    list2.par_iter_mut().for_each(|x| *x *= 2);
    assert_eq!(
        sorted(list2.iter().copied().collect::<Vec<u64>>()),
        (0..500).map(|x| x * 2).collect::<Vec<u64>>()
    );

    // By value.
    let by_val = sorted(list.into_par_iter().collect::<Vec<u64>>());
    assert_eq!(by_val, expected);
}

// ////////////////////////////////////////////////////////////////////////
// Strings

const MIXED: &str = "aé漢🦀x"; // 1-, 2-, 3-, 4-, 1-byte chars

#[test]
fn par_chars_matches_sequential() {
    let s = MIXED.repeat(500);
    let par = sorted(s.par_chars().collect::<Vec<char>>());
    let seq = sorted(s.chars().collect::<Vec<char>>());
    assert_eq!(par, seq);

    assert_eq!("".par_chars().count(), 0);
    assert_eq!("z".par_chars().collect::<Vec<char>>(), vec!['z']);
}

#[test]
fn par_char_indices_matches_sequential() {
    let s = MIXED.repeat(300);
    let par = sorted(s.par_char_indices().collect::<Vec<(usize, char)>>());
    let seq = sorted(s.char_indices().collect::<Vec<(usize, char)>>());
    assert_eq!(par, seq);

    assert_eq!("".par_char_indices().count(), 0);
}

#[test]
fn par_bytes_matches_sequential() {
    let s = MIXED.repeat(400);
    let par = sorted(s.par_bytes().collect::<Vec<u8>>());
    let seq = sorted(s.bytes().collect::<Vec<u8>>());
    assert_eq!(par, seq);
    assert_eq!(s.par_bytes().count(), s.len());
    assert_eq!("".par_bytes().count(), 0);
}

#[test]
fn par_lines_matches_sequential() {
    let inputs = [
        "a\nbb\nccc\ndddd",   // no trailing newline
        "a\nbb\nccc\ndddd\n", // trailing \n
        "no newline at all",
        "",                   // empty string
    ];
    for input in inputs {
        let par = sorted(input.par_lines().collect::<Vec<&str>>());
        let seq = sorted(input.lines().collect::<Vec<&str>>());
        assert_eq!(par, seq, "par_lines mismatch on {input:?}");
    }

    // Regression cases (previous LinesProducer::split bugs): \r\n
    // endings, empty lines at split points, multi-byte UTF-8 around the
    // split midpoint.
    for input in [
        "one\r\ntwo\r\nthree",
        "mix\nof\r\nendings\r\n\nx\n",
        "\n",
        "\n\n\n",
        "é漢\n🦀\nascii\n",
    ] {
        let par = sorted(input.par_lines().collect::<Vec<&str>>());
        let seq = sorted(input.lines().collect::<Vec<&str>>());
        assert_eq!(par, seq, "par_lines mismatch on {input:?}");
    }
    // Big versions of the same, so the producer actually splits at many
    // positions.
    let crlf_big = "line one\r\nline two\r\n\r\nline four\r\n".repeat(3000);
    let par = sorted(crlf_big.par_lines().collect::<Vec<&str>>());
    let seq = sorted(crlf_big.lines().collect::<Vec<&str>>());
    assert_eq!(par, seq);
    let multibyte_big = "é漢字🦀 line\n\n".repeat(5000);
    let par = sorted(multibyte_big.par_lines().collect::<Vec<&str>>());
    let seq = sorted(multibyte_big.lines().collect::<Vec<&str>>());
    assert_eq!(par, seq);

    // A large input to force real splitting.
    let big = "line with some text\n".repeat(5000);
    let par = sorted(big.par_lines().collect::<Vec<&str>>());
    let seq = sorted(big.lines().collect::<Vec<&str>>());
    assert_eq!(par, seq);
    assert_eq!(big.par_lines().count(), 5000);
}

#[test]
fn par_split_whitespace_matches_sequential() {
    let inputs = [
        "the quick  brown\tfox",
        "  leading and trailing   ",
        "\t\t tabs \t and\nnewlines \r\n as whitespace \t",
        "single",
        "",
        "   ",
        "é漢 🦀  words",
    ];
    for input in inputs {
        let par = sorted(input.par_split_whitespace().collect::<Vec<&str>>());
        let seq = sorted(input.split_whitespace().collect::<Vec<&str>>());
        assert_eq!(par, seq, "par_split_whitespace mismatch on {input:?}");
    }

    let big = "alpha beta\tgamma  delta ".repeat(3000);
    let par = sorted(big.par_split_whitespace().collect::<Vec<&str>>());
    let seq = sorted(big.split_whitespace().collect::<Vec<&str>>());
    assert_eq!(par, seq);
}

// ////////////////////////////////////////////////////////////////////////
// Collect targets / FromParallelIterator / ParallelExtend

#[test]
fn collect_vec_indexed_and_unindexed_paths() {
    // Indexed (exact-len in-place path).
    let indexed: Vec<u64> = (0..10_000u64).into_par_iter().map(|x| x ^ 1).collect();
    assert_eq!(indexed, (0..10_000u64).map(|x| x ^ 1).collect::<Vec<u64>>());

    // Unindexed (through filter, per-leaf buffers).
    let unindexed: Vec<u64> = (0..10_000u64)
        .into_par_iter()
        .filter(|x| x % 7 != 0)
        .collect();
    assert_eq!(
        unindexed,
        (0..10_000u64).filter(|x| x % 7 != 0).collect::<Vec<u64>>()
    );

    // Empty.
    let empty: Vec<u64> = (0..0u64).into_par_iter().collect();
    assert!(empty.is_empty());
}

#[test]
fn collect_vecdeque_and_linkedlist() {
    let dq: VecDeque<u64> = (0..2000u64).into_par_iter().map(|x| x + 5).collect();
    assert_eq!(
        dq.into_iter().collect::<Vec<u64>>(),
        (5..2005u64).collect::<Vec<u64>>()
    );

    let ll: LinkedList<u64> = (0..2000u64).into_par_iter().collect();
    assert_eq!(
        ll.into_iter().collect::<Vec<u64>>(),
        (0..2000u64).collect::<Vec<u64>>()
    );
}

#[test]
fn collect_string_from_char_str_and_string() {
    // From char (indexed source: order must be preserved).
    let chars: Vec<char> = "hello parallel world! é漢🦀".chars().collect();
    let s: String = chars.par_iter().copied().collect();
    assert_eq!(s, "hello parallel world! é漢🦀");

    // From &str.
    let parts: Vec<&str> = vec!["par", "allel", " ", "str", "ings"];
    let s: String = parts.par_iter().copied().collect();
    assert_eq!(s, "parallel strings");

    // From String.
    let s: String = (0..100u32).into_par_iter().map(|i| i.to_string()).collect();
    let seq: String = (0..100u32).map(|i| i.to_string()).collect();
    assert_eq!(s, seq);
}

#[test]
fn collect_hashmap_and_hashset() {
    let map: HashMap<u32, u64> = (0..1000u32).into_par_iter().map(|i| (i, i as u64 * 2)).collect();
    assert_eq!(map.len(), 1000);
    for (k, v) in &map {
        assert_eq!(*v, *k as u64 * 2);
    }

    let set: HashSet<u64> = (0..1000u64).into_par_iter().map(|x| x % 100).collect();
    assert_eq!(set, (0..100u64).collect::<HashSet<u64>>());
}

#[test]
fn collect_btreemap_and_btreeset() {
    let map: BTreeMap<u32, u32> = (0..500u32).into_par_iter().map(|i| (i, i * i)).collect();
    assert_eq!(map.len(), 500);
    assert_eq!(
        map.into_iter().collect::<Vec<(u32, u32)>>(),
        (0..500u32).map(|i| (i, i * i)).collect::<Vec<(u32, u32)>>()
    );

    let set: BTreeSet<i32> = (0..1000i32).into_par_iter().map(|x| x % 37).collect();
    assert_eq!(set, (0..37i32).collect::<BTreeSet<i32>>());
}

#[test]
fn collect_binaryheap_and_unit() {
    let heap: BinaryHeap<u64> = lcg_vec(3000, 7)
        .into_par_iter()
        .map(|x| x % 1000)
        .collect();
    let mut expected: Vec<u64> = lcg_vec(3000, 7).iter().map(|x| x % 1000).collect();
    expected.sort();
    assert_eq!(heap.into_sorted_vec(), expected);

    // Collecting () from an iterator of () just drives the pipeline.
    let count = AtomicUsize::new(0);
    #[allow(clippy::unit_arg)]
    let () = (0..5000u64)
        .into_par_iter()
        .map(|_| {
            count.fetch_add(1, Ordering::Relaxed);
        })
        .collect();
    assert_eq!(count.load(Ordering::Relaxed), 5000);
}

#[test]
fn par_extend_targets() {
    // Vec, indexed source (exact-len path appends in place).
    let mut v = vec![1u64, 2, 3];
    v.par_extend((10..20u64).into_par_iter());
    assert_eq!(v, vec![1, 2, 3, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]);

    // Vec, unindexed source.
    let mut v2 = vec![0u64];
    v2.par_extend((0..100u64).into_par_iter().filter(|x| x % 10 == 0));
    assert_eq!(v2, vec![0, 0, 10, 20, 30, 40, 50, 60, 70, 80, 90]);

    // String from chars.
    let mut s = String::from(">> ");
    s.par_extend("abcdef".chars().collect::<Vec<char>>().par_iter().copied());
    assert_eq!(s, ">> abcdef");

    // HashMap.
    let mut map: HashMap<u32, u32> = HashMap::new();
    map.par_extend((0..100u32).into_par_iter().map(|i| (i, i + 1)));
    assert_eq!(map.len(), 100);
    assert_eq!(map[&42], 43);

    // VecDeque.
    let mut dq: VecDeque<u32> = VecDeque::from(vec![7]);
    dq.par_extend((0..50u32).into_par_iter());
    assert_eq!(dq.len(), 51);
    assert_eq!(dq[0], 7);
    assert_eq!(
        dq.into_iter().skip(1).collect::<Vec<u32>>(),
        (0..50u32).collect::<Vec<u32>>()
    );

    // BTreeSet.
    let mut set: BTreeSet<u32> = BTreeSet::new();
    set.par_extend((0..200u32).into_par_iter().map(|x| x % 25));
    assert_eq!(set, (0..25u32).collect::<BTreeSet<u32>>());
}

// ////////////////////////////////////////////////////////////////////////
// scope / spawn / join / thread pool

#[test]
fn scope_spawns_borrow_stack_data() {
    let mut left = 0;
    let mut right = 0;
    filament::scope(|s| {
        s.spawn(|_| left = 1);
        s.spawn(|_| right = 2);
    });
    assert_eq!(left + right, 3);
}

#[test]
fn scope_returns_value() {
    let counter = AtomicUsize::new(0);
    let answer = filament::scope(|s| {
        s.spawn(|_| {
            counter.fetch_add(1, Ordering::Relaxed);
        });
        42
    });
    assert_eq!(answer, 42);
    assert_eq!(counter.load(Ordering::Relaxed), 1, "scope must wait for spawns");
}

#[test]
fn scope_many_spawns() {
    let counter = AtomicUsize::new(0);
    filament::scope(|s| {
        for _ in 0..1000 {
            s.spawn(|_| {
                counter.fetch_add(1, Ordering::Relaxed);
            });
        }
    });
    assert_eq!(counter.load(Ordering::Relaxed), 1000);
}

#[test]
fn scope_nested_spawns() {
    let counter = AtomicUsize::new(0);
    filament::scope(|s| {
        for _ in 0..10 {
            s.spawn(|s2| {
                counter.fetch_add(1, Ordering::Relaxed);
                s2.spawn(|s3| {
                    counter.fetch_add(1, Ordering::Relaxed);
                    s3.spawn(|_| {
                        counter.fetch_add(1, Ordering::Relaxed);
                    });
                });
            });
        }
    });
    assert_eq!(counter.load(Ordering::Relaxed), 30);
}

#[test]
fn scope_spawn_panic_propagates() {
    let result = catch_unwind(AssertUnwindSafe(|| {
        filament::scope(|s| {
            s.spawn(|_| panic!("deliberate panic in spawned task"));
        });
    }));
    assert!(result.is_err(), "panic in spawn must propagate out of scope()");

    // The pool must still be usable afterwards.
    let sum: u64 = (0..10_000u64).into_par_iter().sum();
    assert_eq!(sum, (0..10_000u64).sum::<u64>());
}

#[test]
fn join_basic() {
    let (a, b) = filament::join(
        || (0..1000u64).into_par_iter().sum::<u64>(),
        || (1..=10u64).product::<u64>(),
    );
    assert_eq!(a, (0..1000u64).sum::<u64>());
    assert_eq!(b, 3_628_800);
}

#[test]
fn custom_thread_pool_install() {
    let pool = filament::ThreadPoolBuilder::new()
        .num_threads(2)
        .build()
        .expect("pool builds");
    assert_eq!(pool.current_num_threads(), 2);
    let sum: u64 = pool.install(|| (0..100_000u64).into_par_iter().sum());
    assert_eq!(sum, (0..100_000u64).sum::<u64>());
}

// ////////////////////////////////////////////////////////////////////////
// Parallel sorts

#[test]
fn par_sort_unstable_large_random() {
    let mut v = lcg_vec(150_000, 42);
    let mut expected = v.clone();
    expected.sort_unstable();
    v.par_sort_unstable();
    assert_eq!(v, expected);
}

#[test]
fn par_sort_unstable_special_shapes() {
    // Already sorted.
    let mut v: Vec<u64> = (0..50_000).collect();
    let expected = v.clone();
    v.par_sort_unstable();
    assert_eq!(v, expected);

    // Reverse sorted.
    let mut v: Vec<u64> = (0..50_000).rev().collect();
    v.par_sort_unstable();
    assert_eq!(v, (0..50_000).collect::<Vec<u64>>());

    // All equal.
    let mut v = vec![9u64; 30_000];
    v.par_sort_unstable();
    assert_eq!(v, vec![9u64; 30_000]);

    // Many duplicates.
    let mut v: Vec<u64> = lcg_vec(60_000, 8).iter().map(|x| x % 10).collect();
    let mut expected = v.clone();
    expected.sort_unstable();
    v.par_sort_unstable();
    assert_eq!(v, expected);
}

#[test]
fn par_sort_unstable_tiny_sizes() {
    for n in 0..=3usize {
        // Try every permutation-ish arrangement via LCG shuffles.
        for seed in 0..8u64 {
            let mut s = seed + 1;
            let mut v: Vec<u64> = (0..n as u64).map(|_| lcg(&mut s) % 10).collect();
            let mut expected = v.clone();
            expected.sort_unstable();
            v.par_sort_unstable();
            assert_eq!(v, expected, "n={n} seed={seed}");
        }
    }
}

#[test]
fn par_sort_unstable_by_descending() {
    let mut v = lcg_vec(120_000, 9);
    let mut expected = v.clone();
    expected.sort_unstable_by(|a, b| b.cmp(a));
    v.par_sort_unstable_by(|a, b| b.cmp(a));
    // Elements are plain u64s, so equal keys mean identical values and
    // exact comparison is valid even for an unstable sort.
    assert_eq!(v, expected);
    // And it is exactly the ascending sort reversed.
    let mut asc = v.clone();
    asc.sort_unstable();
    assert_eq!(v, asc.into_iter().rev().collect::<Vec<u64>>());
}

#[test]
fn par_sort_unstable_by_key_correctness() {
    let original = lcg_vec(100_000, 10);
    let mut v = original.clone();
    let key = |x: &u64| *x % 10;
    v.par_sort_unstable_by_key(key);

    // (a) The result is a permutation of the input.
    assert_eq!(sorted(v.clone()), sorted(original));
    // (b) Keys are non-decreasing (unstable: order of equal keys is free).
    assert!(v.windows(2).all(|w| key(&w[0]) <= key(&w[1])));
}

// ////////////////////////////////////////////////////////////////////////
// Panic propagation through pipelines

#[test]
fn map_panic_propagates_and_pool_survives() {
    let result = catch_unwind(AssertUnwindSafe(|| {
        (0..10_000u64)
            .into_par_iter()
            .map(|i| {
                if i == 5_000 {
                    panic!("deliberate panic in map");
                }
                i
            })
            .sum::<u64>()
    }));
    assert!(result.is_err(), "panic inside map must propagate to the caller");

    // The global pool must remain usable after a propagated panic.
    let sum: u64 = (0..50_000u64).into_par_iter().map(|x| x + 1).sum();
    assert_eq!(sum, (1..=50_000u64).sum::<u64>());
    let collected: Vec<u32> = (0..1000u32).into_par_iter().collect();
    assert_eq!(collected, (0..1000u32).collect::<Vec<u32>>());
}

#[test]
fn for_each_panic_propagates() {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let v: Vec<u64> = (0..1000).collect();
        v.par_iter().for_each(|&x| {
            if x == 777 {
                panic!("deliberate panic in for_each");
            }
        });
    }));
    assert!(result.is_err());

    // Still usable.
    assert_eq!((0..100u64).into_par_iter().sum::<u64>(), 4950);
}

// ////////////////////////////////////////////////////////////////////////
// Assorted edge cases

#[test]
fn empty_everything() {
    let empty: Vec<u64> = vec![];
    assert_eq!(empty.par_iter().copied().sum::<u64>(), 0);
    assert_eq!(empty.par_iter().count(), 0);
    assert!(empty.par_iter().copied().collect::<Vec<u64>>().is_empty());
    assert_eq!(empty.par_iter().find_any(|_| true), None);
    assert!(!empty.par_iter().any(|_| true));
    assert!(empty.par_iter().all(|_| false));
    assert_eq!(empty.par_iter().copied().reduce_with(|a, b| a + b), None);
    assert_eq!(
        empty
            .par_iter()
            .copied()
            .fold(|| 0u64, |a, b| a + b)
            .sum::<u64>(),
        0
    );
    let e2: Vec<u64> = empty
        .par_iter()
        .copied()
        .map(|x| x)
        .filter(|_| true)
        .flat_map(|x| vec![x])
        .collect();
    assert!(e2.is_empty());
}

#[test]
fn single_element_pipelines() {
    let one = vec![41u64];
    assert_eq!(one.par_iter().copied().map(|x| x + 1).sum::<u64>(), 42);
    assert_eq!(one.par_iter().copied().reduce_with(|a, b| a + b), Some(41));
    assert_eq!(one.par_iter().copied().rev().collect::<Vec<u64>>(), vec![41]);
    assert_eq!(
        one.par_iter().copied().enumerate().collect::<Vec<(usize, u64)>>(),
        vec![(0, 41)]
    );
    assert_eq!(one.par_iter().len(), 1);
}

#[test]
fn combined_adapter_stack_matches_sequential() {
    // A deep pipeline mixing many adapters at once.
    let par: Vec<u64> = (0..20_000u64)
        .into_par_iter()
        .map(|x| x * 3)
        .filter(|x| x % 2 == 0)
        .map(|x| x / 2)
        .collect();
    let seq: Vec<u64> = (0..20_000u64)
        .map(|x| x * 3)
        .filter(|x| x % 2 == 0)
        .map(|x| x / 2)
        .collect();
    assert_eq!(par, seq);

    let par_sum: u64 = (0..5_000u64)
        .into_par_iter()
        .zip((5_000..10_000u64).into_par_iter())
        .map(|(a, b)| a + b)
        .sum();
    let seq_sum: u64 = (0..5_000u64).zip(5_000..10_000u64).map(|(a, b)| a + b).sum();
    assert_eq!(par_sum, seq_sum);
}
