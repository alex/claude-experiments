//! Runtime SIMD level selection.
//!
//! The level is detected once at startup ([`init`]) and cached in a static;
//! hot paths read it with a single relaxed load.

use crate::arch::cpu::Level;
use core::sync::atomic::{AtomicU8, Ordering};

const UNKNOWN: u8 = 0xff;
static LEVEL: AtomicU8 = AtomicU8::new(UNKNOWN);

/// Detects and caches the SIMD level. Called from process startup.
pub fn init() {
    LEVEL.store(crate::arch::cpu::detect() as u8, Ordering::Relaxed);
}

/// Returns the cached SIMD level, detecting it on first use if startup has
/// not run (host tests).
#[inline(always)]
pub fn level() -> Level {
    match LEVEL.load(Ordering::Relaxed) {
        0 => Level::Sse2,
        1 => Level::Sse42,
        2 => Level::Avx2,
        _ => {
            init();
            level()
        }
    }
}
