//! `<math.h>` over the `libm` crate (the Rust port of musl's libm) and
//! `<fenv.h>`.
//!
//! `long double` variants are not provided: stable Rust cannot express
//! the x87 extended type, and the library treats `long double` as
//! `double` throughout.

use core::ffi::{c_int, c_long, c_longlong};

macro_rules! unary {
    ($($name:ident),* $(,)?) => {
        $(
            #[doc = concat!("`", stringify!($name), "(3)`.")]
            #[cfg_attr(not(test), unsafe(no_mangle))]
            pub extern "C" fn $name(x: f64) -> f64 {
                libm::$name(x)
            }
        )*
    };
}

macro_rules! unaryf {
    ($($name:ident),* $(,)?) => {
        $(
            #[doc = concat!("`", stringify!($name), "(3)`.")]
            #[cfg_attr(not(test), unsafe(no_mangle))]
            pub extern "C" fn $name(x: f32) -> f32 {
                libm::$name(x)
            }
        )*
    };
}

macro_rules! binary {
    ($($name:ident),* $(,)?) => {
        $(
            #[doc = concat!("`", stringify!($name), "(3)`.")]
            #[cfg_attr(not(test), unsafe(no_mangle))]
            pub extern "C" fn $name(x: f64, y: f64) -> f64 {
                libm::$name(x, y)
            }
        )*
    };
}

macro_rules! binaryf {
    ($($name:ident),* $(,)?) => {
        $(
            #[doc = concat!("`", stringify!($name), "(3)`.")]
            #[cfg_attr(not(test), unsafe(no_mangle))]
            pub extern "C" fn $name(x: f32, y: f32) -> f32 {
                libm::$name(x, y)
            }
        )*
    };
}

unary!(
    acos, acosh, asin, asinh, atan, atanh, cbrt, ceil, cos, cosh, erf, erfc, exp, exp10, exp2,
    expm1, fabs, floor, j0, j1, log, log10, log1p, log2, rint, round, sin, sinh, sqrt, tan, tanh,
    tgamma, trunc, y0, y1,
);
unaryf!(
    acosf, acoshf, asinf, asinhf, atanf, atanhf, cbrtf, ceilf, cosf, coshf, erff, erfcf, expf,
    exp10f, exp2f, expm1f, fabsf, floorf, j0f, j1f, logf, log10f, log1pf, log2f, rintf, roundf,
    sinf, sinhf, sqrtf, tanf, tanhf, tgammaf, truncf, y0f, y1f,
);
binary!(
    atan2, copysign, fdim, fmax, fmin, fmod, hypot, nextafter, pow, remainder
);
binaryf!(
    atan2f, copysignf, fdimf, fmaxf, fminf, fmodf, hypotf, nextafterf, powf, remainderf
);

/// `signgam`, set by `lgamma`.
#[cfg_attr(not(test), unsafe(no_mangle))]
#[allow(non_upper_case_globals)]
pub static mut signgam: c_int = 0;

/// `lgamma(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn lgamma(x: f64) -> f64 {
    let (r, sign) = libm::lgamma_r(x);
    // SAFETY: a plain global, as C specifies.
    unsafe { signgam = sign };
    r
}

/// `lgammaf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn lgammaf(x: f32) -> f32 {
    let (r, sign) = libm::lgammaf_r(x);
    // SAFETY: a plain global, as C specifies.
    unsafe { signgam = sign };
    r
}

/// `lgamma_r(3)`.
///
/// # Safety
/// `sign` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn lgamma_r(x: f64, sign: *mut c_int) -> f64 {
    let (r, s) = libm::lgamma_r(x);
    // SAFETY: caller contract.
    unsafe { *sign = s };
    r
}

/// `lgammaf_r(3)`.
///
/// # Safety
/// `sign` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn lgammaf_r(x: f32, sign: *mut c_int) -> f32 {
    let (r, s) = libm::lgammaf_r(x);
    // SAFETY: caller contract.
    unsafe { *sign = s };
    r
}

/// `gamma(3)` (legacy alias of `lgamma`).
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn gamma(x: f64) -> f64 {
    lgamma(x)
}

/// `fma(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn fma(x: f64, y: f64, z: f64) -> f64 {
    libm::fma(x, y, z)
}

/// `fmaf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn fmaf(x: f32, y: f32, z: f32) -> f32 {
    libm::fmaf(x, y, z)
}

/// `frexp(3)`.
///
/// # Safety
/// `exp` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn frexp(x: f64, exp: *mut c_int) -> f64 {
    let (m, e) = libm::frexp(x);
    // SAFETY: caller contract.
    unsafe { *exp = e };
    m
}

/// `frexpf(3)`.
///
/// # Safety
/// `exp` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn frexpf(x: f32, exp: *mut c_int) -> f32 {
    let (m, e) = libm::frexpf(x);
    // SAFETY: caller contract.
    unsafe { *exp = e };
    m
}

/// `ldexp(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn ldexp(x: f64, n: c_int) -> f64 {
    libm::ldexp(x, n)
}

/// `ldexpf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn ldexpf(x: f32, n: c_int) -> f32 {
    libm::ldexpf(x, n)
}

/// `scalbn(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn scalbn(x: f64, n: c_int) -> f64 {
    libm::scalbn(x, n)
}

/// `scalbnf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn scalbnf(x: f32, n: c_int) -> f32 {
    libm::scalbnf(x, n)
}

/// `scalbln(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn scalbln(x: f64, n: c_long) -> f64 {
    libm::scalbn(x, n.clamp(-100_000, 100_000) as c_int)
}

/// `scalblnf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn scalblnf(x: f32, n: c_long) -> f32 {
    libm::scalbnf(x, n.clamp(-100_000, 100_000) as c_int)
}

/// `ilogb(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn ilogb(x: f64) -> c_int {
    libm::ilogb(x)
}

/// `ilogbf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn ilogbf(x: f32) -> c_int {
    libm::ilogbf(x)
}

/// `logb(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn logb(x: f64) -> f64 {
    if x == 0.0 {
        return f64::NEG_INFINITY;
    }
    if x.is_infinite() {
        return f64::INFINITY;
    }
    if x.is_nan() {
        return x;
    }
    libm::ilogb(x) as f64
}

/// `logbf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn logbf(x: f32) -> f32 {
    if x == 0.0 {
        return f32::NEG_INFINITY;
    }
    if x.is_infinite() {
        return f32::INFINITY;
    }
    if x.is_nan() {
        return x;
    }
    libm::ilogbf(x) as f32
}

/// `modf(3)`.
///
/// # Safety
/// `int_part` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn modf(x: f64, int_part: *mut f64) -> f64 {
    let (f, i) = libm::modf(x);
    // SAFETY: caller contract.
    unsafe { *int_part = i };
    f
}

/// `modff(3)`.
///
/// # Safety
/// `int_part` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn modff(x: f32, int_part: *mut f32) -> f32 {
    let (f, i) = libm::modff(x);
    // SAFETY: caller contract.
    unsafe { *int_part = i };
    f
}

/// `remquo(3)`.
///
/// # Safety
/// `quo` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn remquo(x: f64, y: f64, quo: *mut c_int) -> f64 {
    let (r, q) = libm::remquo(x, y);
    // SAFETY: caller contract.
    unsafe { *quo = q };
    r
}

/// `remquof(3)`.
///
/// # Safety
/// `quo` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn remquof(x: f32, y: f32, quo: *mut c_int) -> f32 {
    let (r, q) = libm::remquof(x, y);
    // SAFETY: caller contract.
    unsafe { *quo = q };
    r
}

/// `drem(3)` (legacy alias of `remainder`).
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn drem(x: f64, y: f64) -> f64 {
    libm::remainder(x, y)
}

/// `jn(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn jn(n: c_int, x: f64) -> f64 {
    libm::jn(n, x)
}

/// `jnf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn jnf(n: c_int, x: f32) -> f32 {
    libm::jnf(n, x)
}

/// `yn(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn yn(n: c_int, x: f64) -> f64 {
    libm::yn(n, x)
}

/// `ynf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn ynf(n: c_int, x: f32) -> f32 {
    libm::ynf(n, x)
}

/// `sincos(3)`.
///
/// # Safety
/// Both out-pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sincos(x: f64, s: *mut f64, c: *mut f64) {
    let (a, b) = libm::sincos(x);
    // SAFETY: caller contract.
    unsafe {
        *s = a;
        *c = b;
    }
}

/// `sincosf(3)`.
///
/// # Safety
/// Both out-pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sincosf(x: f32, s: *mut f32, c: *mut f32) {
    let (a, b) = libm::sincosf(x);
    // SAFETY: caller contract.
    unsafe {
        *s = a;
        *c = b;
    }
}

/// `nearbyint(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn nearbyint(x: f64) -> f64 {
    libm::rint(x)
}

/// `nearbyintf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn nearbyintf(x: f32) -> f32 {
    libm::rintf(x)
}

/// Converts a rounded value to an integer, saturating like the hardware
/// does (the result for out-of-range inputs is unspecified by C).
fn to_long(x: f64) -> c_long {
    if x.is_nan() { c_long::MIN } else { x as c_long }
}

/// `lround(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn lround(x: f64) -> c_long {
    to_long(libm::round(x))
}
/// `lroundf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn lroundf(x: f32) -> c_long {
    to_long(libm::roundf(x) as f64)
}
/// `llround(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn llround(x: f64) -> c_longlong {
    to_long(libm::round(x))
}
/// `llroundf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn llroundf(x: f32) -> c_longlong {
    to_long(libm::roundf(x) as f64)
}
/// `lrint(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn lrint(x: f64) -> c_long {
    to_long(libm::rint(x))
}
/// `lrintf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn lrintf(x: f32) -> c_long {
    to_long(libm::rintf(x) as f64)
}
/// `llrint(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn llrint(x: f64) -> c_longlong {
    to_long(libm::rint(x))
}
/// `llrintf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn llrintf(x: f32) -> c_longlong {
    to_long(libm::rintf(x) as f64)
}

/// `nan(3)`: the payload string is ignored.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn nan(_tag: *const crate::c_char) -> f64 {
    f64::NAN
}

/// `nanf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn nanf(_tag: *const crate::c_char) -> f32 {
    f32::NAN
}

/// `significand(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn significand(x: f64) -> f64 {
    if x == 0.0 || !x.is_finite() {
        return x;
    }
    libm::scalbn(x, -libm::ilogb(x))
}

/// `pow10(3)` (legacy alias of `exp10`).
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pow10(x: f64) -> f64 {
    libm::exp10(x)
}

/// Legacy classification functions (the macros in the header use the
/// compiler builtins instead).
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn finite(x: f64) -> c_int {
    x.is_finite() as c_int
}
/// `finitef`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn finitef(x: f32) -> c_int {
    x.is_finite() as c_int
}
/// `__fpclassify`, for code that uses glibc's macro expansion.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn __fpclassify(x: f64) -> c_int {
    classify(x.is_nan(), x.is_infinite(), x == 0.0, x.is_subnormal())
}
/// `__fpclassifyf`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn __fpclassifyf(x: f32) -> c_int {
    classify(x.is_nan(), x.is_infinite(), x == 0.0, x.is_subnormal())
}
fn classify(nan: bool, inf: bool, zero: bool, subnormal: bool) -> c_int {
    // FP_NAN 0, FP_INFINITE 1, FP_ZERO 2, FP_SUBNORMAL 3, FP_NORMAL 4.
    if nan {
        0
    } else if inf {
        1
    } else if zero {
        2
    } else if subnormal {
        3
    } else {
        4
    }
}
/// `__signbit`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn __signbit(x: f64) -> c_int {
    x.is_sign_negative() as c_int
}
/// `__signbitf`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn __signbitf(x: f32) -> c_int {
    x.is_sign_negative() as c_int
}

// ---------------------------------------------------------------------
// fenv.

pub use crate::arch::fenv::*;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spot_checks() {
        assert_eq!(sqrt(16.0), 4.0);
        assert!((sin(core::f64::consts::FRAC_PI_2) - 1.0).abs() < 1e-15);
        assert_eq!(pow(2.0, 10.0), 1024.0);
        assert_eq!(fmod(7.5, 2.0), 1.5);
        assert_eq!(lround(2.5), 3);
        assert_eq!(lround(-2.5), -3);
        assert_eq!(lrint(2.5), 2);
        assert_eq!(logb(8.0), 3.0);
        assert_eq!(logb(0.0), f64::NEG_INFINITY);
        let mut e = 0;
        // SAFETY: valid pointer.
        assert_eq!(unsafe { frexp(8.0, &mut e) }, 0.5);
        assert_eq!(e, 4);
        assert_eq!(__fpclassify(0.0), 2);
        assert_eq!(__fpclassify(f64::NAN), 0);
        assert_eq!(__fpclassify(1e-310), 3);
        assert!(nan(core::ptr::null()).is_nan());
        assert_eq!(fegetround(), FE_TONEAREST);
        assert_eq!(fesetround(FE_UPWARD), 0);
        assert_eq!(fegetround(), FE_UPWARD);
        assert_eq!(fesetround(FE_TONEAREST), 0);
        assert_eq!(fesetround(7), -1);
        assert_eq!(feclearexcept(FE_ALL_EXCEPT), 0);
        assert_eq!(fetestexcept(FE_ALL_EXCEPT), 0);
        assert_eq!(feraiseexcept(FE_INEXACT), 0);
        assert_eq!(fetestexcept(FE_ALL_EXCEPT), FE_INEXACT);
        assert_eq!(feclearexcept(FE_INEXACT), 0);
        assert_eq!(fetestexcept(FE_ALL_EXCEPT), 0);
    }
}
