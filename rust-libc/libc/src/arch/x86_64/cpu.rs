//! CPU feature detection via `cpuid`.

use core::arch::x86_64::{__cpuid, __cpuid_count, _xgetbv};

/// SIMD feature levels the library can dispatch on, in increasing order.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[repr(u8)]
pub enum Level {
    /// Baseline x86_64: SSE2 is always available.
    Sse2 = 0,
    /// SSE4.2 (and everything below it).
    Sse42 = 1,
    /// AVX2 with OS support for saving the upper halves of the YMM registers.
    Avx2 = 2,
}

/// Queries the CPU for the best supported [`Level`].
pub fn detect() -> Level {
    let leaf1 = __cpuid(1);
    let sse42 = leaf1.ecx & (1 << 20) != 0;
    let osxsave = leaf1.ecx & (1 << 27) != 0;
    let avx = leaf1.ecx & (1 << 28) != 0;
    if !sse42 {
        return Level::Sse2;
    }
    if !(osxsave && avx) {
        return Level::Sse42;
    }
    // SAFETY: OSXSAVE is set, so xgetbv(0) is a valid instruction.
    let xcr0 = unsafe { _xgetbv(0) };
    let ymm_state = xcr0 & 0b110 == 0b110;
    let leaf7 = __cpuid_count(7, 0);
    let avx2 = leaf7.ebx & (1 << 5) != 0;
    if ymm_state && avx2 { Level::Avx2 } else { Level::Sse42 }
}
