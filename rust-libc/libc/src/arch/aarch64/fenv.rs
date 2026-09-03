//! `<fenv.h>` on AArch64: the `FPCR` (control) and `FPSR` (status)
//! registers. Exceptions are never trapped, so raising one just sets its
//! flag.

use core::arch::asm;
use core::ffi::c_int;

#[allow(missing_docs)]
pub const FE_INVALID: c_int = 1;
#[allow(missing_docs)]
pub const FE_DIVBYZERO: c_int = 2;
#[allow(missing_docs)]
pub const FE_OVERFLOW: c_int = 4;
#[allow(missing_docs)]
pub const FE_UNDERFLOW: c_int = 8;
#[allow(missing_docs)]
pub const FE_INEXACT: c_int = 16;
#[allow(missing_docs)]
pub const FE_ALL_EXCEPT: c_int = 31;
#[allow(missing_docs)]
pub const FE_TONEAREST: c_int = 0;
#[allow(missing_docs)]
pub const FE_UPWARD: c_int = 0x40_0000;
#[allow(missing_docs)]
pub const FE_DOWNWARD: c_int = 0x80_0000;
#[allow(missing_docs)]
pub const FE_TOWARDZERO: c_int = 0xc0_0000;

const ROUND_MASK: u64 = 0xc0_0000;

/// `fenv_t`: the control register followed by the status register.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct FEnv {
    fpcr: u32,
    fpsr: u32,
}

/// `fexcept_t`.
pub type FExcept = u32;

fn get_fpcr() -> u64 {
    let v: u64;
    // SAFETY: reads a system register.
    unsafe { asm!("mrs {}, fpcr", out(reg) v, options(nomem, nostack, preserves_flags)) };
    v
}

fn set_fpcr(v: u64) {
    // SAFETY: writes the floating-point control register.
    unsafe { asm!("msr fpcr, {}", in(reg) v, options(nomem, nostack, preserves_flags)) };
}

fn get_fpsr() -> u64 {
    let v: u64;
    // SAFETY: reads a system register.
    unsafe { asm!("mrs {}, fpsr", out(reg) v, options(nomem, nostack, preserves_flags)) };
    v
}

fn set_fpsr(v: u64) {
    // SAFETY: writes the floating-point status register.
    unsafe { asm!("msr fpsr, {}", in(reg) v, options(nomem, nostack, preserves_flags)) };
}

/// `fegetround(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn fegetround() -> c_int {
    (get_fpcr() & ROUND_MASK) as c_int
}

/// `fesetround(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn fesetround(mode: c_int) -> c_int {
    if mode as u64 & !ROUND_MASK != 0 {
        return -1;
    }
    set_fpcr((get_fpcr() & !ROUND_MASK) | mode as u64);
    0
}

/// `fetestexcept(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn fetestexcept(mask: c_int) -> c_int {
    (get_fpsr() as c_int) & mask & FE_ALL_EXCEPT
}

/// `feclearexcept(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn feclearexcept(mask: c_int) -> c_int {
    set_fpsr(get_fpsr() & !((mask & FE_ALL_EXCEPT) as u64));
    0
}

/// `feraiseexcept(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn feraiseexcept(mask: c_int) -> c_int {
    set_fpsr(get_fpsr() | (mask & FE_ALL_EXCEPT) as u64);
    0
}

/// `fegetexceptflag(3)`.
///
/// # Safety
/// `flag` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fegetexceptflag(flag: *mut FExcept, mask: c_int) -> c_int {
    // SAFETY: caller contract.
    unsafe { *flag = fetestexcept(mask) as FExcept };
    0
}

/// `fesetexceptflag(3)`.
///
/// # Safety
/// `flag` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fesetexceptflag(flag: *const FExcept, mask: c_int) -> c_int {
    // SAFETY: caller contract.
    let f = unsafe { *flag } as c_int & mask;
    feclearexcept(mask);
    feraiseexcept(f)
}

/// `fegetenv(3)`.
///
/// # Safety
/// `env` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fegetenv(env: *mut FEnv) -> c_int {
    // SAFETY: caller contract.
    unsafe {
        *env = FEnv {
            fpcr: get_fpcr() as u32,
            fpsr: get_fpsr() as u32,
        }
    };
    0
}

/// `fesetenv(3)`. `FE_DFL_ENV` is `(fenv_t *)-1`.
///
/// # Safety
/// `env` must be valid or `FE_DFL_ENV`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fesetenv(env: *const FEnv) -> c_int {
    let e = if env as usize == usize::MAX {
        FEnv { fpcr: 0, fpsr: 0 }
    } else {
        // SAFETY: caller contract.
        unsafe { *env }
    };
    set_fpcr(e.fpcr as u64);
    set_fpsr(e.fpsr as u64);
    0
}

/// `feholdexcept(3)`: exceptions are never trapped here, so this is
/// `fegetenv` plus clearing the flags.
///
/// # Safety
/// `env` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn feholdexcept(env: *mut FEnv) -> c_int {
    // SAFETY: forwarded.
    unsafe { fegetenv(env) };
    feclearexcept(FE_ALL_EXCEPT);
    // Clear the trap-enable bits (8..=12) as well.
    set_fpcr(get_fpcr() & !0x1f00);
    0
}

/// `feupdateenv(3)`.
///
/// # Safety
/// `env` must be valid or `FE_DFL_ENV`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn feupdateenv(env: *const FEnv) -> c_int {
    let raised = fetestexcept(FE_ALL_EXCEPT);
    // SAFETY: forwarded.
    unsafe { fesetenv(env) };
    feraiseexcept(raised)
}
