//! Runtime SIMD level selection and dispatch.
//!
//! The level is detected once at startup ([`init`]) and cached in a static;
//! hot paths read it with a single relaxed load. Kernels are written once,
//! generic over [`Lanes`](crate::string::lanes::Lanes), and the
//! [`dispatch_fn!`] macro instantiates them for every supported level inside
//! a function that has that level's target features enabled, so the
//! intrinsics inline into it.

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

/// Returns the cached SIMD level. Process startup runs [`init`] before
/// anything else can run; if it somehow has not happened yet the baseline
/// is used, which is always correct. (Host tests, which have no startup
/// code, detect lazily instead.)
#[inline(always)]
pub fn level() -> Level {
    #[cfg(test)]
    {
        match LEVEL_FOR_TESTS.load(Ordering::Relaxed) {
            0 => return Level::Sse2,
            1 => return Level::Avx2,
            2 => return Level::Avx512,
            _ => {}
        }
    }
    match LEVEL.load(Ordering::Relaxed) {
        1 => Level::Avx2,
        2 => Level::Avx512,
        #[cfg(test)]
        UNKNOWN => detect_slow(),
        _ => Level::Sse2,
    }
}

#[cfg(test)]
#[cold]
#[inline(never)]
fn detect_slow() -> Level {
    init();
    level()
}

/// True if 32-byte AVX2 vectors may be used.
#[inline(always)]
pub fn has_avx2() -> bool {
    level() >= Level::Avx2
}

/// Defines a function that dispatches on the detected level to one
/// instantiation per backend of a kernel generic over `L: Lanes`.
///
/// ```ignore
/// dispatch_fn! {
///     /// Docs.
///     pub unsafe fn strlen(s: *const u8) -> usize = strlen_k;
/// }
/// ```
///
/// Each instantiation is a separate `#[target_feature]` function taking
/// the same arguments in registers, so the kernel and every intrinsic it
/// uses inline into it, and the dispatcher itself is a load, a compare
/// and a tail call (much like an ifunc). The `unsafe` variants forward
/// the caller's safety obligation to the kernel.
///
/// `dispatch_fn_ymm!` is the same but never uses 64-byte vectors: on
/// current CPUs a 64-byte store cannot forward to a narrower load, which
/// makes copies that are read back immediately much slower, so the
/// store-heavy kernels stop at AVX2.
macro_rules! dispatch_fn {
    ($(#[$m:meta])* $vis:vis unsafe fn $name:ident($($arg:ident: $ty:ty),* $(,)?) -> $ret:ty = $kernel:ident;) => {
        $(#[$m])*
        #[inline(always)]
        $vis unsafe fn $name($($arg: $ty),*) -> $ret {
            $crate::string::simd::dispatch_body!(zmm, $kernel, ($($arg: $ty),*) -> $ret)
        }
    };
    ($(#[$m:meta])* $vis:vis fn $name:ident($($arg:ident: $ty:ty),* $(,)?) -> $ret:ty = $kernel:ident;) => {
        $(#[$m])*
        #[inline(always)]
        $vis fn $name($($arg: $ty),*) -> $ret {
            $crate::string::simd::dispatch_body!(zmm, $kernel, ($($arg: $ty),*) -> $ret)
        }
    };
}
pub(crate) use dispatch_fn;

/// See [`dispatch_fn!`].
macro_rules! dispatch_fn_ymm {
    ($(#[$m:meta])* $vis:vis unsafe fn $name:ident($($arg:ident: $ty:ty),* $(,)?) -> $ret:ty = $kernel:ident;) => {
        $(#[$m])*
        #[inline(always)]
        $vis unsafe fn $name($($arg: $ty),*) -> $ret {
            $crate::string::simd::dispatch_body!(ymm, $kernel, ($($arg: $ty),*) -> $ret)
        }
    };
}
pub(crate) use dispatch_fn_ymm;

/// Body shared by the dispatch macros.
macro_rules! dispatch_body {
    (zmm, $kernel:ident, ($($arg:ident: $ty:ty),*) -> $ret:ty) => {{
        #[allow(unused_unsafe)]
        #[target_feature(enable = "avx2,avx512f,avx512bw")]
        unsafe fn avx512($($arg: $ty),*) -> $ret {
            // SAFETY: the caller's contract, forwarded.
            unsafe { $kernel::<$crate::string::lanes::Avx512>($($arg),*) }
        }
        #[allow(unused_unsafe)]
        #[target_feature(enable = "avx2")]
        unsafe fn avx2($($arg: $ty),*) -> $ret {
            // SAFETY: the caller's contract, forwarded.
            unsafe { $kernel::<$crate::string::lanes::Avx2>($($arg),*) }
        }
        #[allow(unused_unsafe)]
        unsafe fn sse2($($arg: $ty),*) -> $ret {
            // SAFETY: the caller's contract, forwarded.
            unsafe { $kernel::<$crate::string::lanes::Sse2>($($arg),*) }
        }
        // SAFETY: `level()` only reports a level after cpuid confirmed its
        // features; the kernels' own contracts are the caller's.
        unsafe {
            match $crate::string::simd::level() {
                $crate::arch::cpu::Level::Avx512 => avx512($($arg),*),
                $crate::arch::cpu::Level::Avx2 => avx2($($arg),*),
                $crate::arch::cpu::Level::Sse2 => sse2($($arg),*),
            }
        }
    }};
    (ymm, $kernel:ident, ($($arg:ident: $ty:ty),*) -> $ret:ty) => {{
        #[allow(unused_unsafe)]
        #[target_feature(enable = "avx2")]
        unsafe fn avx2($($arg: $ty),*) -> $ret {
            // SAFETY: the caller's contract, forwarded.
            unsafe { $kernel::<$crate::string::lanes::Avx2>($($arg),*) }
        }
        #[allow(unused_unsafe)]
        unsafe fn sse2($($arg: $ty),*) -> $ret {
            // SAFETY: the caller's contract, forwarded.
            unsafe { $kernel::<$crate::string::lanes::Sse2>($($arg),*) }
        }
        // SAFETY: as above.
        unsafe {
            match $crate::string::simd::level() {
                $crate::arch::cpu::Level::Avx512 | $crate::arch::cpu::Level::Avx2 => {
                    avx2($($arg),*)
                }
                $crate::arch::cpu::Level::Sse2 => sse2($($arg),*),
            }
        }
    }};
}
pub(crate) use dispatch_body;
