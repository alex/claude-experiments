//! `<fenv.h>` on x86_64: the x87 control/status words and the SSE
//! `MXCSR` register are kept in sync, as glibc does.

use core::arch::asm;
use core::ffi::c_int;

#[allow(missing_docs)]
pub const FE_INVALID: c_int = 1;
#[allow(missing_docs)]
pub const FE_DIVBYZERO: c_int = 4;
#[allow(missing_docs)]
pub const FE_OVERFLOW: c_int = 8;
#[allow(missing_docs)]
pub const FE_UNDERFLOW: c_int = 16;
#[allow(missing_docs)]
pub const FE_INEXACT: c_int = 32;
#[allow(missing_docs)]
pub const FE_ALL_EXCEPT: c_int = 63;
#[allow(missing_docs)]
pub const FE_TONEAREST: c_int = 0;
#[allow(missing_docs)]
pub const FE_DOWNWARD: c_int = 0x400;
#[allow(missing_docs)]
pub const FE_UPWARD: c_int = 0x800;
#[allow(missing_docs)]
pub const FE_TOWARDZERO: c_int = 0xc00;

/// `fenv_t`: the x87 environment (28 bytes) followed by MXCSR.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct FEnv {
    x87: [u32; 7],
    mxcsr: u32,
}

/// `fexcept_t`.
pub type FExcept = u16;

fn get_mxcsr() -> u32 {
    let mut v: u32 = 0;
    // SAFETY: stores MXCSR to a stack slot.
    unsafe { asm!("stmxcsr [{}]", in(reg) &mut v, options(nostack, preserves_flags)) };
    v
}

fn set_mxcsr(v: u32) {
    // SAFETY: loads MXCSR from a stack slot; the value is masked so
    // reserved bits stay zero.
    unsafe { asm!("ldmxcsr [{}]", in(reg) &(v & 0xffff), options(nostack, preserves_flags)) };
}

fn get_x87_cw() -> u16 {
    let mut v: u16 = 0;
    // SAFETY: stores the x87 control word to a stack slot.
    unsafe { asm!("fnstcw [{}]", in(reg) &mut v, options(nostack, preserves_flags)) };
    v
}

fn set_x87_cw(v: u16) {
    // SAFETY: loads the x87 control word.
    unsafe { asm!("fldcw [{}]", in(reg) &v, options(nostack, preserves_flags)) };
}

fn get_x87_sw() -> u16 {
    let v: u16;
    // SAFETY: stores the x87 status word in ax.
    unsafe { asm!("fnstsw ax", out("ax") v, options(nostack, preserves_flags)) };
    v
}

fn get_x87_env() -> [u32; 7] {
    let mut env = [0u32; 7];
    // SAFETY: `fnstenv` writes 28 bytes and masks all exceptions; the
    // control word is restored right after as glibc does.
    unsafe {
        asm!("fnstenv [{}]", in(reg) env.as_mut_ptr(), options(nostack, preserves_flags));
        asm!("fldcw [{}]", in(reg) env.as_ptr(), options(nostack, preserves_flags));
    }
    env
}

fn set_x87_env(env: &[u32; 7]) {
    // SAFETY: loads a 28-byte environment previously stored by `fnstenv`.
    unsafe { asm!("fldenv [{}]", in(reg) env.as_ptr(), options(nostack, preserves_flags)) };
}

/// `fegetround(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn fegetround() -> c_int {
    (get_x87_cw() & 0xc00) as c_int
}

/// `fesetround(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn fesetround(mode: c_int) -> c_int {
    if mode & !0xc00 != 0 {
        return -1;
    }
    set_x87_cw((get_x87_cw() & !0xc00) | mode as u16);
    set_mxcsr((get_mxcsr() & !0x6000) | ((mode as u32) << 3));
    0
}

/// `fetestexcept(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn fetestexcept(mask: c_int) -> c_int {
    ((get_x87_sw() as c_int | get_mxcsr() as c_int) & mask) & FE_ALL_EXCEPT
}

/// `feclearexcept(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn feclearexcept(mask: c_int) -> c_int {
    let mask = (mask & FE_ALL_EXCEPT) as u32;
    let mut env = get_x87_env();
    env[1] &= !mask; // status word is the second dword
    set_x87_env(&env);
    set_mxcsr(get_mxcsr() & !mask);
    0
}

/// `feraiseexcept(3)`: sets the flags in MXCSR (exceptions are masked
/// there, so no trap results).
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn feraiseexcept(mask: c_int) -> c_int {
    set_mxcsr(get_mxcsr() | (mask & FE_ALL_EXCEPT) as u32);
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
            x87: get_x87_env(),
            mxcsr: get_mxcsr(),
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
    if env as usize == usize::MAX {
        // Default: round to nearest, all exceptions masked, flags clear.
        let mut x87 = get_x87_env();
        x87[0] = (x87[0] & !0xffff) | 0x37f;
        x87[1] &= !0xffff;
        set_x87_env(&x87);
        set_mxcsr(0x1f80);
        return 0;
    }
    // SAFETY: caller contract.
    let e = unsafe { *env };
    set_x87_env(&e.x87);
    set_mxcsr(e.mxcsr);
    0
}

/// `feholdexcept(3)`.
///
/// # Safety
/// `env` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn feholdexcept(env: *mut FEnv) -> c_int {
    // SAFETY: forwarded.
    unsafe { fegetenv(env) };
    feclearexcept(FE_ALL_EXCEPT);
    // Mask all exceptions.
    set_x87_cw(get_x87_cw() | 0x3f);
    set_mxcsr(get_mxcsr() | 0x1f80);
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
