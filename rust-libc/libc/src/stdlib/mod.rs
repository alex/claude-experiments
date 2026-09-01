//! `<stdlib.h>` (the parts that are not the allocator or process exit).
//!
//! * [`num`]  – `strtol`/`strtod` families and `atoi` & co,
//! * [`sort`] – `qsort`, `qsort_r`, `bsearch`,
//! * [`env`]  – `getenv`, `setenv`, `putenv`, `unsetenv`, `clearenv`,
//! * [`rand`] – `rand`, `srand`, `rand_r`, `random`, `srandom`.

pub mod env;
pub mod num;
pub mod rand;
pub mod sort;

use core::ffi::{c_int, c_long, c_longlong};

/// `abs(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn abs(x: c_int) -> c_int {
    x.wrapping_abs()
}

/// `labs(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn labs(x: c_long) -> c_long {
    x.wrapping_abs()
}

/// `llabs(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn llabs(x: c_longlong) -> c_longlong {
    x.wrapping_abs()
}

/// `div_t`.
#[repr(C)]
pub struct DivT {
    /// Quotient.
    pub quot: c_int,
    /// Remainder.
    pub rem: c_int,
}

/// `ldiv_t`.
#[repr(C)]
pub struct LdivT {
    /// Quotient.
    pub quot: c_long,
    /// Remainder.
    pub rem: c_long,
}

/// `div(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn div(num: c_int, den: c_int) -> DivT {
    DivT {
        quot: num.wrapping_div(den),
        rem: num.wrapping_rem(den),
    }
}

/// `ldiv(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn ldiv(num: c_long, den: c_long) -> LdivT {
    LdivT {
        quot: num.wrapping_div(den),
        rem: num.wrapping_rem(den),
    }
}

/// `lldiv(3)`. `lldiv_t` has the same layout as `ldiv_t` on x86_64.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn lldiv(num: c_longlong, den: c_longlong) -> LdivT {
    LdivT {
        quot: num.wrapping_div(den),
        rem: num.wrapping_rem(den),
    }
}

/// `imaxabs(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn imaxabs(x: i64) -> i64 {
    x.wrapping_abs()
}

/// `imaxdiv(3)`; `imaxdiv_t` has the same layout as `ldiv_t`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn imaxdiv(num: i64, den: i64) -> LdivT {
    LdivT {
        quot: num.wrapping_div(den),
        rem: num.wrapping_rem(den),
    }
}
