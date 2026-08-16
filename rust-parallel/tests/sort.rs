// quick sanity of sorts incl. panic safety & stability, before the big test suite lands
use filament::prelude::*;

struct DropCounter(u32, std::sync::Arc<std::sync::atomic::AtomicUsize>);
impl Drop for DropCounter {
    fn drop(&mut self) { self.1.fetch_add(1, std::sync::atomic::Ordering::Relaxed); }
}

fn lcg_vec(n: usize, m: u64) -> Vec<u64> {
    let mut s = 0x12345678u64;
    (0..n).map(|_| { s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); (s >> 33) % m }).collect()
}

#[test]
fn sort_sanity_suite() {
    // unstable
    let mut v = lcg_vec(1_000_000, u64::MAX);
    let mut w = v.clone();
    v.par_sort_unstable();
    w.sort_unstable();
    assert_eq!(v, w);
    // dup-heavy
    let mut v = lcg_vec(1_000_000, 10);
    let mut w = v.clone();
    v.par_sort_unstable();
    w.sort_unstable();
    assert_eq!(v, w);
    // stable + stability check: sort pairs by key only, payload order must be preserved
    let base = lcg_vec(500_000, 100);
    let mut pairs: Vec<(u64, usize)> = base.iter().copied().zip(0..).collect();
    let mut expect = pairs.clone();
    pairs.par_sort_by(|a, b| a.0.cmp(&b.0));
    expect.sort_by(|a, b| a.0.cmp(&b.0)); // std stable
    assert_eq!(pairs, expect, "stability violated");
    // stable with strings (drop-sensitive type)
    let mut sv: Vec<String> = lcg_vec(300_000, 1000).into_iter().map(|x| format!("{x:05}")).collect();
    let mut sw = sv.clone();
    sv.par_sort();
    sw.sort();
    assert_eq!(sv, sw);
    // panic in comparator: every element dropped exactly once, no double free
    let drops = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let n = 200_000;
    let mut dv: Vec<DropCounter> = lcg_vec(n, 1000).into_iter().map(|x| DropCounter(x as u32, drops.clone())).collect();
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        dv.par_sort_by(|a, b| {
            if a.0 == 777 && b.0 == 777 { panic!("comparator boom"); }
            a.0.cmp(&b.0)
        });
    }));
    assert!(r.is_err(), "expected panic");
    drop(dv);
    assert_eq!(drops.load(std::sync::atomic::Ordering::Relaxed), n, "drop count mismatch => ownership bug");
    // same for unstable
    let drops2 = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let mut dv2: Vec<DropCounter> = lcg_vec(n, 1000).into_iter().map(|x| DropCounter(x as u32, drops2.clone())).collect();
    let r2 = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        dv2.par_sort_unstable_by(|a, b| {
            if a.0 == 777 && b.0 == 777 { panic!("boom2"); }
            a.0.cmp(&b.0)
        });
    }));
    assert!(r2.is_err());
    drop(dv2);
    assert_eq!(drops2.load(std::sync::atomic::Ordering::Relaxed), n);
    
}
