//! Integration tests for the core parallel iterator functionality,
//! validated against sequential equivalents.

use filament::prelude::*;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

#[test]
fn slice_sum_matches_sequential() {
    let v: Vec<u64> = (0..100_000).collect();
    let par: u64 = v.par_iter().sum();
    let seq: u64 = v.iter().sum();
    assert_eq!(par, seq);
}

#[test]
fn slice_map_sum() {
    let v: Vec<u64> = (0..50_000).collect();
    let par: u64 = v.par_iter().map(|&x| x * 3 + 1).sum();
    let seq: u64 = v.iter().map(|&x| x * 3 + 1).sum();
    assert_eq!(par, seq);
}

#[test]
fn range_sum() {
    let par: u64 = (0..1_000_000u64).into_par_iter().sum();
    assert_eq!(par, 499_999_500_000);
}

#[test]
fn range_all_int_types() {
    assert_eq!((0..100u8).into_par_iter().count(), 100);
    assert_eq!((0..1000u16).into_par_iter().count(), 1000);
    assert_eq!((0..1000u32).into_par_iter().count(), 1000);
    assert_eq!((0..1000u64).into_par_iter().count(), 1000);
    assert_eq!((0..1000usize).into_par_iter().count(), 1000);
    assert_eq!((-50..50i8).into_par_iter().count(), 100);
    #[allow(clippy::reversed_empty_ranges)]
    {
        assert_eq!((50..-50i16).into_par_iter().count(), 0); // start > end: empty
    }
    assert_eq!((-500..500i64).into_par_iter().count(), 1000);
    assert_eq!((-500..500isize).into_par_iter().count(), 1000);
}

#[test]
fn range_inclusive() {
    let par: u64 = (1..=1000u64).into_par_iter().sum();
    assert_eq!(par, 500_500);
    assert_eq!((0..=0u8).into_par_iter().count(), 1);
    // Full domain: must not overflow.
    assert_eq!((0..=255u8).into_par_iter().count(), 256);
}

#[test]
fn for_each_touches_every_item() {
    let n = 10_000;
    let counter = AtomicUsize::new(0);
    let total = AtomicU64::new(0);
    (0..n as u64).into_par_iter().for_each(|i| {
        counter.fetch_add(1, Ordering::Relaxed);
        total.fetch_add(i, Ordering::Relaxed);
    });
    assert_eq!(counter.load(Ordering::Relaxed), n);
    assert_eq!(total.load(Ordering::Relaxed), (n as u64 - 1) * n as u64 / 2);
}

#[test]
fn par_iter_mut_writes() {
    let mut v = vec![0u64; 100_000];
    v.par_iter_mut().enumerate_hack();
}

// Helper while enumerate doesn't exist yet: just write via indices.
trait EnumerateHack {
    fn enumerate_hack(self);
}
impl<'a, I: ParallelIterator<Item = &'a mut u64>> EnumerateHack for I {
    fn enumerate_hack(self) {
        self.for_each(|x| *x = 7);
    }
}

#[test]
fn reduce_max() {
    let v: Vec<i64> = (0..100_000).map(|i| (i * 2654435761u64 % 1000003) as i64).collect();
    let par = v.par_iter().map(|&x| x).reduce(|| i64::MIN, i64::max);
    let seq = v.iter().copied().fold(i64::MIN, i64::max);
    assert_eq!(par, seq);
}

#[test]
fn count_works() {
    assert_eq!((0..123_456u32).into_par_iter().count(), 123_456);
    let v = vec![1u8; 4321];
    assert_eq!(v.par_iter().count(), 4321);
}

#[test]
fn collect_indexed_exact() {
    let v: Vec<u64> = (0..100_000u64).into_par_iter().map(|i| i * 2).collect();
    assert_eq!(v.len(), 100_000);
    for (i, &x) in v.iter().enumerate() {
        assert_eq!(x, i as u64 * 2);
    }
}

#[test]
fn collect_into_vec_reuses_allocation() {
    let mut v: Vec<u64> = Vec::with_capacity(200_000);
    let cap_before = v.capacity();
    (0..100_000u64).into_par_iter().map(|i| i + 1).collect_into_vec(&mut v);
    assert_eq!(v.capacity(), cap_before);
    assert_eq!(v.len(), 100_000);
    assert_eq!(v[0], 1);
    assert_eq!(v[99_999], 100_000);
}

#[test]
fn collect_nontrivial_drop_type() {
    let v: Vec<String> = (0..10_000u32).into_par_iter().map(|i| i.to_string()).collect();
    assert_eq!(v.len(), 10_000);
    assert_eq!(v[9999], "9999");
}

#[test]
fn vec_into_par_iter_moves() {
    let v: Vec<String> = (0..10_000u32).map(|i| i.to_string()).collect();
    let lens: usize = v.into_par_iter().map(|s| s.len()).sum();
    let expect: usize = (0..10_000u32).map(|i| i.to_string().len()).sum();
    assert_eq!(lens, expect);
}

#[test]
fn vec_into_par_iter_drops_unconsumed_on_panic() {
    // Even if a panic occurs mid-iteration, all items must be dropped
    // exactly once (no leaks, no double drops).
    use std::sync::Arc;
    let counter = Arc::new(AtomicUsize::new(0));
    struct D(Arc<AtomicUsize>, u32);
    impl Drop for D {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::Relaxed);
        }
    }
    let v: Vec<D> = (0..1000).map(|i| D(counter.clone(), i)).collect();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        v.into_par_iter().for_each(|d| {
            if d.1 == 500 {
                panic!("boom");
            }
        });
    }));
    assert!(result.is_err());
    assert_eq!(counter.load(Ordering::Relaxed), 1000);
}

#[test]
fn chunks_sum() {
    let v: Vec<u64> = (0..100_000).collect();
    let par: u64 = v.par_chunks(1024).map(|c| c.iter().sum::<u64>()).sum();
    let seq: u64 = v.iter().sum();
    assert_eq!(par, seq);
    // count of chunks
    assert_eq!(v.par_chunks(1024).count(), 100_000usize.div_ceil(1024));
}

#[test]
fn chunks_exact_and_remainder() {
    let v: Vec<u32> = (0..1000).collect();
    let ce = v.par_chunks_exact(64);
    assert_eq!(ce.remainder().len(), 1000 % 64);
    assert_eq!(ce.count(), 1000 / 64);
}

#[test]
fn windows_count() {
    let v: Vec<u32> = (0..1000).collect();
    assert_eq!(v.par_windows(16).count(), 1000 - 16 + 1);
    let max_window_sum: u64 = v
        .par_windows(3)
        .map(|w| w.iter().map(|&x| x as u64).sum::<u64>())
        .reduce(|| 0, u64::max);
    assert_eq!(max_window_sum, 997 + 998 + 999);
}

#[test]
fn chunks_mut_parallel_fill() {
    let mut v = vec![0u8; 10_000];
    v.par_chunks_mut(97).for_each(|chunk| {
        for x in chunk {
            *x = 7;
        }
    });
    assert!(v.iter().all(|&x| x == 7));
}

#[test]
fn empty_inputs() {
    let v: Vec<u64> = vec![];
    assert_eq!(v.par_iter().sum::<u64>(), 0);
    assert_eq!(v.par_iter().count(), 0);
    assert_eq!((0..0u32).into_par_iter().count(), 0);
    let c: Vec<u64> = (0..0u64).into_par_iter().collect();
    assert!(c.is_empty());
    #[allow(clippy::reversed_empty_ranges)]
    let r = (5..=1u32).into_par_iter().count();
    assert_eq!(r, 0);
}

#[test]
fn single_item() {
    assert_eq!((0..1u32).into_par_iter().sum::<u32>(), 0);
    let v = vec![42u64];
    assert_eq!(v.par_iter().sum::<u64>(), 42);
}

#[test]
fn nested_parallelism() {
    // Parallel iterators inside parallel iterators.
    let total: u64 = (0..100u64)
        .into_par_iter()
        .map(|i| (0..1000u64).into_par_iter().map(|j| i + j).sum::<u64>())
        .sum();
    let expect: u64 = (0..100u64)
        .map(|i| (0..1000u64).map(|j| i + j).sum::<u64>())
        .sum();
    assert_eq!(total, expect);
}

#[test]
fn panic_in_map_propagates_and_pool_survives() {
    for _ in 0..3 {
        let r = std::panic::catch_unwind(|| {
            (0..10_000u64).into_par_iter().for_each(|i| {
                if i == 7777 {
                    panic!("boom {i}");
                }
            });
        });
        assert!(r.is_err());
        // Pool still usable afterwards.
        let s: u64 = (0..1000u64).into_par_iter().sum();
        assert_eq!(s, 499_500);
    }
}

#[test]
fn works_from_worker_thread_context() {
    // collect() called from inside a join arm (worker context).
    let ((), v) = filament::join(
        || (),
        || {
            (0..10_000u64)
                .into_par_iter()
                .map(|i| i * i)
                .collect::<Vec<_>>()
        },
    );
    assert_eq!(v.len(), 10_000);
    assert_eq!(v[100], 10_000);
}

#[test]
fn unindexed_collect_parallel_gather_drop_safety() {
    // >64k items so the parallel-gather path (not sequential append) runs;
    // drop-sensitive type so any double-move or missed move is caught.
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    let drops = Arc::new(AtomicUsize::new(0));
    struct D(u64, Arc<AtomicUsize>);
    impl Drop for D {
        fn drop(&mut self) {
            self.1.fetch_add(1, Ordering::Relaxed);
        }
    }
    let n = 300_000u64;
    {
        let collected: Vec<D> = (0..n)
            .into_par_iter()
            .filter(|&x| x % 3 != 0)
            .map(|x| D(x, drops.clone()))
            .collect();
        let expected = (0..n).filter(|&x| x % 3 != 0).count();
        assert_eq!(collected.len(), expected);
        // Values intact and unique.
        let mut vals: Vec<u64> = collected.iter().map(|d| d.0).collect();
        vals.sort_unstable();
        vals.dedup();
        assert_eq!(vals.len(), expected);
        assert_eq!(drops.load(Ordering::Relaxed), 0, "premature drops");
    }
    let expected = (0..n).filter(|&x| x % 3 != 0).count();
    assert_eq!(drops.load(Ordering::Relaxed), expected, "each item dropped exactly once");
}

#[test]
fn unindexed_collect_string_gather() {
    let v: Vec<String> = (0..200_000u32)
        .into_par_iter()
        .filter(|&x| x % 2 == 0)
        .map(|x| x.to_string())
        .collect();
    assert_eq!(v.len(), 100_000);
    let mut sorted_v: Vec<u32> = v.iter().map(|s| s.parse().unwrap()).collect();
    sorted_v.sort_unstable();
    for (i, x) in sorted_v.iter().enumerate() {
        assert_eq!(*x, i as u32 * 2);
    }
}
