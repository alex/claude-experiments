//! Pseudo-random numbers: `rand`, `srand`, `rand_r`, `random`, `srandom`.
//!
//! `rand`/`random` share one generator: a 64-bit xorshift* (period
//! 2^64-1, good statistical quality, no lookup tables). The sequence is
//! deterministic for a given seed as C requires, but not the same as any
//! other libc's. `rand_r` uses a 32-bit state of the caller's.
//!
//! None of these are suitable for anything security related; use
//! `getrandom`/`arc4random` for that.

use core::ffi::{c_int, c_long, c_uint};
use core::sync::atomic::{AtomicU64, Ordering};

/// `RAND_MAX`.
pub const RAND_MAX: c_int = 0x7fff_ffff;

static STATE: AtomicU64 = AtomicU64::new(SEED_DEFAULT);
const SEED_DEFAULT: u64 = 0x2545_f491_4f6c_dd1d; // srand(1) equivalent

fn seed_to_state(seed: u64) -> u64 {
    // Never let the state become zero (xorshift's fixed point).
    let s = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ 0x2545_f491_4f6c_dd1d;
    if s == 0 { SEED_DEFAULT } else { s }
}

fn next(state: &AtomicU64) -> u64 {
    // A compare-exchange loop keeps the sequence consistent even when
    // several threads share the generator.
    let mut s = state.load(Ordering::Relaxed);
    loop {
        let mut x = s;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        match state.compare_exchange_weak(s, x, Ordering::Relaxed, Ordering::Relaxed) {
            Ok(_) => return x.wrapping_mul(0x2545_f491_4f6c_dd1d),
            Err(v) => s = v,
        }
    }
}

/// `srand(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn srand(seed: c_uint) {
    STATE.store(seed_to_state(seed as u64), Ordering::Relaxed);
}

/// `rand(3)`: returns a value in `[0, RAND_MAX]`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn rand() -> c_int {
    (next(&STATE) >> 33) as c_int
}

/// `srandom(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn srandom(seed: c_uint) {
    srand(seed)
}

/// `random(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn random() -> c_long {
    rand() as c_long
}

/// `rand_r(3)`: a reentrant generator with 32 bits of caller-owned state.
///
/// # Safety
/// `seed` must be a valid pointer.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn rand_r(seed: *mut c_uint) -> c_int {
    // SAFETY: caller contract.
    unsafe {
        // xorshift32 followed by a multiplicative hash of the output.
        let mut x = *seed;
        if x == 0 {
            x = 0x9e37_79b9;
        }
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        *seed = x;
        (x.wrapping_mul(0x2c1b_3c6d) >> 1) as c_int
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_and_in_range() {
        srand(7);
        let a: Vec<c_int> = (0..10).map(|_| rand()).collect();
        srand(7);
        let b: Vec<c_int> = (0..10).map(|_| rand()).collect();
        assert_eq!(a, b);
        assert!(a.iter().all(|&v| (0..=RAND_MAX).contains(&v)));
        assert!(a.windows(2).any(|w| w[0] != w[1]));
        srand(8);
        let c: Vec<c_int> = (0..10).map(|_| rand()).collect();
        assert_ne!(a, c);
        let mut s = 0u32;
        // SAFETY: valid pointer.
        let (x, y) = unsafe { (rand_r(&mut s), rand_r(&mut s)) };
        assert_ne!(x, y);
        assert!(x >= 0 && y >= 0);
        assert!(random() >= 0);
    }
}
