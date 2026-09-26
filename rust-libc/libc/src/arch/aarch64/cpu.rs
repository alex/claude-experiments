//! CPU feature detection. NEON is part of the AArch64 baseline, so there
//! is a single level; the SIMD kernels' AVX levels are x86_64 only.

/// SIMD feature levels the library can dispatch on.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[repr(u8)]
pub enum Level {
    /// Baseline AArch64: NEON (Advanced SIMD).
    Neon = 0,
}

/// Queries the CPU for the best supported [`Level`].
pub fn detect() -> Level {
    Level::Neon
}
