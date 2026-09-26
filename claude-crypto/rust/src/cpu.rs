//! Run-time CPU feature detection (x86-64), usable without `std`.

use core::arch::x86_64::{CpuidResult, __cpuid, __cpuid_count, _xgetbv};
use core::sync::atomic::{AtomicU8, Ordering};

/// Which verified implementation the CPU can run.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum X86Level {
    /// Neither verified implementation is usable (pre-Haswell CPUs).
    Baseline,
    /// BMI1 + BMI2 + MOVBE: `cc_sha256_blocks_x86_scalar`.
    Bmi2,
    /// AVX2 + BMI1 + BMI2 (+ MOVBE) with OS support for the YMM state:
    /// `cc_sha256_blocks_x86_avx2`.
    Avx2,
}

/// Detected features: the `X86Level` in bits 0–1 (1, 2, 3), `SHA_NI`, and
/// `DETECTED` once detection has run.
static FEATURES: AtomicU8 = AtomicU8::new(0);
const SHA_NI: u8 = 0x40;
const DETECTED: u8 = 0x80;

#[target_feature(enable = "xsave")]
unsafe fn xcr0() -> u64 {
    _xgetbv(0)
}

fn detect() -> u8 {
    // SAFETY: CPUID is available on every x86-64 CPU.
    let (l1, l7) = unsafe { (__cpuid(1), __cpuid_count(7, 0)) };
    // The SHA extensions (CPUID.(EAX=7,ECX=0):EBX[29]) and SSSE3 (CPUID.1:ECX[9]):
    // `cc_sha256_blocks_x86_shani` (legacy-SSE encodings only, so no OS
    // support beyond SSE is needed).
    let sha_ni = l7.ebx & (1 << 29) != 0 && l1.ecx & (1 << 9) != 0;
    let level = match detect_level(&l1, &l7) {
        X86Level::Baseline => 1,
        X86Level::Bmi2 => 2,
        X86Level::Avx2 => 3,
    };
    DETECTED | level | if sha_ni { SHA_NI } else { 0 }
}

/// The `X86Level`, from CPUID leaves 1 and 7 (subleaf 0).
fn detect_level(l1: &CpuidResult, l7: &CpuidResult) -> X86Level {
    let movbe = l1.ecx & (1 << 22) != 0;
    let osxsave = l1.ecx & (1 << 27) != 0;
    let avx = l1.ecx & (1 << 28) != 0;
    let bmi1 = l7.ebx & (1 << 3) != 0;
    let avx2 = l7.ebx & (1 << 5) != 0;
    let bmi2 = l7.ebx & (1 << 8) != 0;
    if !(bmi1 && bmi2 && movbe) {
        return X86Level::Baseline;
    }
    // SAFETY: XGETBV is available when OSXSAVE is set.
    let ymm_enabled = osxsave && (unsafe { xcr0() } & 0b110) == 0b110;
    if avx && avx2 && ymm_enabled {
        X86Level::Avx2
    } else {
        X86Level::Bmi2
    }
}

/// The detected features (detected once).
#[inline]
fn features() -> u8 {
    let f = FEATURES.load(Ordering::Relaxed);
    if f & DETECTED != 0 {
        f
    } else {
        let f = detect();
        FEATURES.store(f, Ordering::Relaxed);
        f
    }
}

/// The best implementation level of this CPU (detected once).
#[inline]
pub(crate) fn x86_level() -> X86Level {
    match features() & 3 {
        1 => X86Level::Baseline,
        2 => X86Level::Bmi2,
        _ => X86Level::Avx2,
    }
}

/// Whether CPUID reports the SHA extensions and SSSE3, as required by
/// `cc_sha256_blocks_x86_shani` (independent of `x86_level`: e.g. Goldmont
/// has SHA-NI but no AVX2 or BMI2).
#[inline]
pub(crate) fn has_sha_ni() -> bool {
    features() & SHA_NI != 0
}
