//! Test order randomisation — pytest-randomly's behaviour, built in.
//!
//! Items are shuffled at three levels (modules, classes within a module, tests
//! within a class), so ordering assumptions break loudly while related tests
//! stay adjacent.  Keeping modules contiguous also matters for us: it is what
//! lets module scoped fixtures live for a single contiguous span.

use std::sync::Arc;

use crate::session::Item;

/// xorshift64*: small, fast, and reproducible across platforms so a seed
/// always reproduces the same order.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed.wrapping_mul(0x9E3779B97F4A7C15).max(1))
    }

    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }

    pub fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            return 0;
        }
        (self.next_u64() % n as u64) as usize
    }

    pub fn shuffle<T>(&mut self, v: &mut [T]) {
        for i in (1..v.len()).rev() {
            let j = self.below(i + 1);
            v.swap(i, j);
        }
    }
}

/// Derive the session seed from the `--randomly-seed` option.
pub fn resolve_seed(opt: &str) -> u64 {
    match opt {
        "" | "default" => {
            // pytest-randomly picks a fresh seed per run; mirror that so
            // ordering assumptions surface, while still printing the seed.
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos() as u64)
                .unwrap_or(0x5EED)
                % 4_294_967_296
        }
        "last" => std::fs::read_to_string(".pytest_rs_seed")
            .ok()
            .and_then(|s| s.trim().parse().ok())
            .unwrap_or(0),
        other => other.parse().unwrap_or(0),
    }
}

#[allow(dead_code)]
pub fn save_seed(seed: u64) {
    let _ = std::fs::write(".pytest_rs_seed", seed.to_string());
}

/// Shuffle modules, then classes inside each module, then tests inside each
/// class, keeping every level contiguous.
pub fn reorder(items: &mut Vec<Arc<Item>>, seed: u64) {
    let mut rng = Rng::new(seed);
    // Bucket by module preserving first-seen order.
    let mut modules: Vec<String> = Vec::new();
    let mut by_module: std::collections::HashMap<String, Vec<Arc<Item>>> = std::collections::HashMap::new();
    for it in items.drain(..) {
        let key = it.relpath.clone();
        if !by_module.contains_key(&key) {
            modules.push(key.clone());
        }
        by_module.entry(key).or_default().push(it);
    }
    rng.shuffle(&mut modules);
    for m in modules {
        let mut group = by_module.remove(&m).unwrap_or_default();
        // Bucket by class within the module.
        let mut classes: Vec<Option<String>> = Vec::new();
        let mut by_class: std::collections::HashMap<Option<String>, Vec<Arc<Item>>> = std::collections::HashMap::new();
        for it in group.drain(..) {
            let key = it.cls_name.clone();
            if !by_class.contains_key(&key) {
                classes.push(key.clone());
            }
            by_class.entry(key).or_default().push(it);
        }
        rng.shuffle(&mut classes);
        for c in classes {
            let mut tests = by_class.remove(&c).unwrap_or_default();
            rng.shuffle(&mut tests);
            items.extend(tests);
        }
    }
}

/// Reseed Python's global RNG.  Only safe when a single test can be running.
pub fn reseed_python(py: pyo3::Python<'_>, seed: u64) -> pyo3::PyResult<()> {
    use pyo3::prelude::*;
    let random = py.import("random")?;
    random.call_method1("seed", (seed,))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shuffle_is_deterministic() {
        let mut a: Vec<u32> = (0..50).collect();
        let mut b = a.clone();
        Rng::new(1234).shuffle(&mut a);
        Rng::new(1234).shuffle(&mut b);
        assert_eq!(a, b);
        assert_ne!(a, (0..50).collect::<Vec<u32>>());
    }
}
