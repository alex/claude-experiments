//! Run-time CPU feature detection (x86-64), usable without `std`.

use core::arch::x86_64::{__cpuid, __cpuid_count, _xgetbv};
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

static LEVEL: AtomicU8 = AtomicU8::new(0);

#[target_feature(enable = "xsave")]
unsafe fn xcr0() -> u64 {
    _xgetbv(0)
}

fn detect() -> X86Level {
    // SAFETY: CPUID is available on every x86-64 CPU.
    let (l1, l7) = unsafe { (__cpuid(1), __cpuid_count(7, 0)) };
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

/// The best implementation level of this CPU (detected once).
#[inline]
pub(crate) fn x86_level() -> X86Level {
    match LEVEL.load(Ordering::Relaxed) {
        1 => X86Level::Baseline,
        2 => X86Level::Bmi2,
        3 => X86Level::Avx2,
        _ => {
            let l = detect();
            LEVEL.store(
                match l {
                    X86Level::Baseline => 1,
                    X86Level::Bmi2 => 2,
                    X86Level::Avx2 => 3,
                },
                Ordering::Relaxed,
            );
            l
        }
    }
}
