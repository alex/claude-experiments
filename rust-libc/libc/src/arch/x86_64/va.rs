//! The SysV x86_64 `va_list` and the variadic entry point stubs.
//!
//! Rust cannot define C-variadic functions on stable, so every variadic
//! C entry point (`printf`, `scanf`, …) is a tiny assembly stub generated
//! by [`variadic_stub!`]. The stub spills the argument registers into a
//! register save area exactly as a C compiler's prologue would, builds a
//! `va_list` describing it, and tail-calls the `v*` implementation with
//! that `va_list` appended to the fixed arguments.
//!
//! [`VaList`] then reads arguments the way `va_arg` does: integers and
//! pointers from the six general purpose slots then the stack, doubles
//! from the eight XMM slots then the stack, and `long double` always from
//! the stack (16-byte aligned).

use core::ffi::c_void;

/// `struct __va_list_tag`.
#[repr(C)]
pub struct VaList {
    gp_offset: u32,
    fp_offset: u32,
    overflow_arg_area: *mut u8,
    reg_save_area: *mut u8,
}

const GP_END: u32 = 6 * 8;
const FP_END: u32 = GP_END + 8 * 16;

impl VaList {
    /// Reads the next integer or pointer argument (`va_arg(ap, long)`).
    ///
    /// # Safety
    /// The caller must have supplied such an argument.
    #[inline]
    pub unsafe fn gp(&mut self) -> u64 {
        // SAFETY: the areas were laid out by the stub / the C compiler.
        unsafe {
            if self.gp_offset < GP_END {
                let v = *(self.reg_save_area.add(self.gp_offset as usize) as *const u64);
                self.gp_offset += 8;
                v
            } else {
                let v = *(self.overflow_arg_area as *const u64);
                self.overflow_arg_area = self.overflow_arg_area.add(8);
                v
            }
        }
    }

    /// Reads the next `double` argument.
    ///
    /// # Safety
    /// The caller must have supplied such an argument.
    #[inline]
    pub unsafe fn fp(&mut self) -> f64 {
        // SAFETY: as in `gp`.
        unsafe {
            if self.fp_offset < FP_END {
                let v = *(self.reg_save_area.add(self.fp_offset as usize) as *const f64);
                self.fp_offset += 16;
                v
            } else {
                let v = *(self.overflow_arg_area as *const f64);
                self.overflow_arg_area = self.overflow_arg_area.add(8);
                v
            }
        }
    }

    /// Reads the next `long double` argument, converted to `f64`
    /// (this library only supports double precision).
    ///
    /// # Safety
    /// The caller must have supplied such an argument.
    #[inline]
    pub unsafe fn long_double(&mut self) -> f64 {
        // SAFETY: long doubles are always passed in memory, 16-byte aligned.
        unsafe {
            let p = ((self.overflow_arg_area as usize + 15) & !15) as *const u8;
            let mantissa = *(p as *const u64);
            let se = *(p.add(8) as *const u16);
            self.overflow_arg_area = p.add(16) as *mut u8;
            x87_to_f64(mantissa, se)
        }
    }

    /// Reads the next pointer argument.
    ///
    /// # Safety
    /// The caller must have supplied such an argument.
    #[inline]
    pub unsafe fn ptr(&mut self) -> *mut c_void {
        // SAFETY: forwarded.
        unsafe { self.gp() as usize as *mut c_void }
    }
}

/// Converts an 80-bit x87 extended value to `f64` (round to nearest even).
pub fn x87_to_f64(mantissa: u64, se: u16) -> f64 {
    let sign = (se >> 15) as u64;
    let exp = (se & 0x7fff) as i32;
    if exp == 0x7fff {
        // Infinity or NaN (the integer bit and payload distinguish them).
        return if mantissa << 1 == 0 {
            if sign == 1 {
                f64::NEG_INFINITY
            } else {
                f64::INFINITY
            }
        } else {
            f64::NAN
        };
    }
    if mantissa == 0 {
        return if sign == 1 { -0.0 } else { 0.0 };
    }
    // Value = mantissa * 2^(exp - 16383 - 63). Normalise (pseudo-denormals
    // may have the integer bit clear).
    let shift = mantissa.leading_zeros();
    let m = mantissa << shift;
    let e = exp - 16383 - shift as i32; // exponent of the leading bit
    if e > 1023 {
        return if sign == 1 {
            f64::NEG_INFINITY
        } else {
            f64::INFINITY
        };
    }
    let keep: i32 = if e >= -1022 { 53 } else { 53 - (-1022 - e) };
    if keep <= 0 {
        let v = if keep == 0 && m > 1 << 63 {
            f64::from_bits(1)
        } else {
            0.0
        };
        return if sign == 1 { -v } else { v };
    }
    let drop = 64 - keep as u32;
    let mut kept = m >> drop;
    let rem = m & ((1u64 << drop) - 1);
    let half = 1u64 << (drop - 1);
    if rem > half || (rem == half && kept & 1 == 1) {
        kept += 1;
    }
    let mut e = e;
    if kept >> keep == 1 {
        if keep < 53 {
            // A subnormal that carried into the next bit already has the
            // right encoding (possibly DBL_MIN).
            return f64::from_bits(kept | (sign << 63));
        }
        kept >>= 1;
        e += 1;
        if e > 1023 {
            return if sign == 1 {
                f64::NEG_INFINITY
            } else {
                f64::INFINITY
            };
        }
    }
    let bits = if e >= -1022 {
        (((e + 1023) as u64) << 52) | (kept & ((1 << 52) - 1))
    } else {
        kept
    };
    f64::from_bits(bits | (sign << 63))
}

/// Stores `v` as a C `long double` (the 80-bit x87 format) at `dst`.
///
/// # Safety
/// `dst` must be valid for 16 bytes.
pub unsafe fn write_long_double(dst: *mut u8, v: f64) {
    let (m, se) = f64_to_x87(v);
    // SAFETY: caller contract.
    unsafe {
        (dst as *mut u64).write_unaligned(m);
        (dst.add(8) as *mut u16).write_unaligned(se);
    }
}

/// Converts an `f64` to the 80-bit x87 extended format (mantissa with
/// explicit integer bit, and sign+exponent word).
pub fn f64_to_x87(x: f64) -> (u64, u16) {
    let bits = x.to_bits();
    let sign = ((bits >> 63) as u16) << 15;
    let exp = ((bits >> 52) & 0x7ff) as i32;
    let frac = bits & ((1u64 << 52) - 1);
    if exp == 0x7ff {
        // Infinity: integer bit set, rest zero. NaN: quiet bit set too.
        return if frac == 0 {
            (1 << 63, sign | 0x7fff)
        } else {
            (0xc000_0000_0000_0000, sign | 0x7fff)
        };
    }
    if exp == 0 {
        if frac == 0 {
            return (0, sign);
        }
        // Subnormal: normalise.
        let shift = frac.leading_zeros() - 11;
        let m = (frac << shift) << 11;
        return (m, sign | (16383 - 1022 - shift as i32) as u16);
    }
    let m = ((1u64 << 52) | frac) << 11;
    (m, sign | (exp - 1023 + 16383) as u16)
}

/// Defines a variadic C entry point `$name` with `$fixed` fixed
/// arguments that calls `$target` with those arguments followed by a
/// pointer to the `va_list`. `$reg` is the register the pointer goes in
/// (the one after the fixed arguments).
#[cfg(not(test))]
macro_rules! variadic_stub {
    ($name:ident, $fixed:tt, $target:path) => {
        core::arch::global_asm!(
            concat!(".globl ", stringify!($name)),
            concat!(".type ", stringify!($name), ",@function"),
            concat!(stringify!($name), ":"),
            // Frame: 176 bytes of register save area, 24 bytes of va_list,
            // and 200 keeps the stack 16-byte aligned for the call.
            "sub rsp, 200",
            "mov [rsp], rdi",
            "mov [rsp + 8], rsi",
            "mov [rsp + 16], rdx",
            "mov [rsp + 24], rcx",
            "mov [rsp + 32], r8",
            "mov [rsp + 40], r9",
            "test al, al",
            "je 1f",
            "movaps [rsp + 48], xmm0",
            "movaps [rsp + 64], xmm1",
            "movaps [rsp + 80], xmm2",
            "movaps [rsp + 96], xmm3",
            "movaps [rsp + 112], xmm4",
            "movaps [rsp + 128], xmm5",
            "movaps [rsp + 144], xmm6",
            "movaps [rsp + 160], xmm7",
            "1:",
            concat!("mov dword ptr [rsp + 176], ", stringify!($fixed), " * 8"),
            "mov dword ptr [rsp + 180], 48",
            "lea rax, [rsp + 208]",
            "mov [rsp + 184], rax",
            "mov [rsp + 192], rsp",
            concat!("lea ", $crate::arch::va::arg_reg!($fixed), ", [rsp + 176]"),
            "call {target}",
            "add rsp, 200",
            "ret",
            concat!(".size ", stringify!($name), ", .-", stringify!($name)),
            target = sym $target,
        );
    };
}
#[cfg(not(test))]
pub(crate) use variadic_stub;

/// The register holding integer argument number `n` (0-based) in the
/// SysV calling convention, as an assembler operand.
macro_rules! arg_reg {
    (1) => {
        "rsi"
    };
    (2) => {
        "rdx"
    };
    (3) => {
        "rcx"
    };
    (4) => {
        "r8"
    };
    (5) => {
        "r9"
    };
}
#[cfg(not(test))]
pub(crate) use arg_reg;

/// Defines `$name`, a function with `$target`'s arguments that returns
/// `$target`'s `double` result as a C `long double` (on x86_64 in
/// `st(0)`).
macro_rules! long_double_stub {
    ($name:ident, $target:path) => {
        core::arch::global_asm!(
            concat!(".globl ", stringify!($name)),
            concat!(".type ", stringify!($name), ",@function"),
            concat!(stringify!($name), ":"),
            "sub rsp, 8",
            "call {target}",
            "movsd qword ptr [rsp], xmm0",
            "fld qword ptr [rsp]",
            "add rsp, 8",
            "ret",
            concat!(".size ", stringify!($name), ", .-", stringify!($name)),
            target = sym $target,
        );
    };
}
#[cfg(not(test))]
pub(crate) use long_double_stub;



#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn x87_round_trip() {
        for x in [
            0.0,
            -0.0,
            1.0,
            -1.5,
            core::f64::consts::PI,
            1e300,
            1e-300,
            f64::MIN_POSITIVE,
            f64::from_bits(1),
            f64::MAX,
            f64::INFINITY,
            f64::NEG_INFINITY,
        ] {
            let (m, se) = f64_to_x87(x);
            assert_eq!(x87_to_f64(m, se).to_bits(), x.to_bits(), "{x}");
        }
        let (m, se) = f64_to_x87(f64::NAN);
        assert!(x87_to_f64(m, se).is_nan());
    }

    #[test]
    fn x87_conversion() {
        // 1.0 = mantissa 0x8000000000000000, exponent 16383.
        assert_eq!(x87_to_f64(0x8000_0000_0000_0000, 16383), 1.0);
        assert_eq!(x87_to_f64(0x8000_0000_0000_0000, 16383 | 0x8000), -1.0);
        assert_eq!(x87_to_f64(0xc000_0000_0000_0000, 16384), 3.0);
        assert_eq!(x87_to_f64(0, 0), 0.0);
        assert!(x87_to_f64(0, 0x8000).is_sign_negative());
        assert_eq!(x87_to_f64(0x8000_0000_0000_0000, 0x7fff), f64::INFINITY);
        assert!(x87_to_f64(0xc000_0000_0000_0000, 0x7fff).is_nan());
        assert_eq!(
            x87_to_f64(0x8000_0000_0000_0000, 16383 + 1024),
            f64::INFINITY
        );
        // pi as an 80-bit value rounds to the f64 pi.
        assert_eq!(
            x87_to_f64(0xc90f_daa2_2168_c235, 16384),
            core::f64::consts::PI
        );
        // Smallest f64 subnormal.
        assert_eq!(
            x87_to_f64(0x8000_0000_0000_0000, 16383 - 1074),
            f64::from_bits(1)
        );
        assert_eq!(x87_to_f64(0x8000_0000_0000_0000, 16383 - 1076), 0.0);
        // A subnormal that rounds up to DBL_MIN (2^-1022 - 2^-1086).
        assert_eq!(
            x87_to_f64(0xffff_ffff_ffff_ffff, 16383 - 1023),
            f64::MIN_POSITIVE
        );
        assert_eq!(
            x87_to_f64(0xffff_ffff_ffff_ffff, (16383 - 1023) | 0x8000),
            -f64::MIN_POSITIVE
        );
        // Round half to even at the 53-bit boundary: 1 + 2^-53 -> 1.0,
        // 1 + 2^-53 + 2^-63 -> 1 + 2^-52.
        assert_eq!(x87_to_f64(0x8000_0000_0000_0400, 16383), 1.0);
        assert_eq!(x87_to_f64(0x8000_0000_0000_0401, 16383), 1.0 + f64::EPSILON);
        assert_eq!(
            x87_to_f64(0x8000_0000_0000_0c00, 16383),
            1.0 + 2.0 * f64::EPSILON
        );
    }
}
