//! Runtime SIMD level selection and dispatch.
//!
//! The level is detected once at startup ([`init`]) and cached in a static;
//! hot paths read it with a single relaxed load. Kernels are written once,
//! generic over [`fearless_simd::Simd`], and the [`dispatch!`] macro
//! instantiates them for every supported level.

use crate::arch::cpu::Level;
use core::sync::atomic::{AtomicU8, Ordering};

const UNKNOWN: u8 = 0xff;
static LEVEL: AtomicU8 = AtomicU8::new(UNKNOWN);

/// Detects and caches the SIMD level. Called from process startup.
pub fn init() {
    LEVEL.store(crate::arch::cpu::detect() as u8, Ordering::Relaxed);
}

/// Host tests use this to force a level below what the CPU supports.
#[cfg(test)]
pub static LEVEL_FOR_TESTS: AtomicU8 = AtomicU8::new(UNKNOWN);

/// Returns the cached SIMD level, detecting it on first use if startup has
/// not run (host tests).
#[inline(always)]
pub fn level() -> Level {
    #[cfg(test)]
    {
        match LEVEL_FOR_TESTS.load(Ordering::Relaxed) {
            0 => return Level::Sse2,
            1 => return Level::Avx2,
            _ => {}
        }
    }
    match LEVEL.load(Ordering::Relaxed) {
        0 => Level::Sse2,
        1 => Level::Avx2,
        _ => {
            init();
            level()
        }
    }
}

/// Runs `$body` with `$simd` bound to the SIMD token for the detected
/// level. `$body` should call an `#[inline(always)]` kernel generic over
/// `S: Simd`, so that the compiler produces one fully inlined copy per
/// level inside a function that has that level's target features enabled.
macro_rules! dispatch {
    ($simd:ident => $body:expr) => {{
        use fearless_simd::Simd as _;
        match $crate::string::simd::level() {
            $crate::arch::cpu::Level::Avx2 => {
                // SAFETY: `level()` only reports Avx2 after cpuid confirmed it.
                let token = unsafe { fearless_simd::Avx2::assume_supported() };
                token.vectorize(
                    #[inline(always)]
                    || {
                        let $simd = token;
                        $body
                    },
                )
            }
            $crate::arch::cpu::Level::Sse2 => {
                // SAFETY: SSE2 is part of the x86_64 baseline.
                let $simd = unsafe { fearless_simd::Sse2::assume_supported() };
                $body
            }
        }
    }};
}
pub(crate) use dispatch;
