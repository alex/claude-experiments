//! Numeric conversions: `strtol`, `strtod` and friends.
//!
//! The decimal floating-point path hands the validated numeric prefix to
//! `core`'s `f64::from_str`, which is correctly rounded for any input
//! length. Hexadecimal floats are converted here with round-half-even.

use crate::c_char;
use crate::errno::Errno;
use core::ffi::{c_int, c_long, c_longlong, c_ulong, c_ulonglong};
use core::ptr;

/// Bytes C's `isspace` accepts.
fn is_space(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r')
}

/// Reads bytes of a NUL-terminated string lazily.
struct Cursor {
    ptr: *const u8,
    pos: usize,
}

impl Cursor {
    /// # Safety
    /// `ptr` must be NUL-terminated.
    unsafe fn new(ptr: *const u8) -> Self {
        Cursor { ptr, pos: 0 }
    }

    #[inline]
    fn peek(&self) -> u8 {
        // SAFETY: never reads past the terminator (peek at NUL returns it).
        unsafe { *self.ptr.add(self.pos) }
    }

    #[inline]
    fn peek_at(&self, off: usize) -> u8 {
        let mut i = 0;
        while i < off {
            // SAFETY: stops at the terminator.
            if unsafe { *self.ptr.add(self.pos + i) } == 0 {
                return 0;
            }
            i += 1;
        }
        // SAFETY: all bytes before were non-NUL.
        unsafe { *self.ptr.add(self.pos + off) }
    }

    #[inline]
    fn bump(&mut self) -> u8 {
        let b = self.peek();
        self.pos += 1;
        b
    }

    /// Consumes `word` case-insensitively if present.
    fn eat_ci(&mut self, word: &[u8]) -> bool {
        for (i, &w) in word.iter().enumerate() {
            if self.peek_at(i).to_ascii_lowercase() != w {
                return false;
            }
        }
        self.pos += word.len();
        true
    }
}

/// Result of scanning an integer.
struct IntScan {
    /// Magnitude, saturated at `u64::MAX` when `overflow` is set.
    magnitude: u64,
    negative: bool,
    overflow: bool,
    /// Offset of the first byte after the number, or 0 if no digits.
    end: usize,
}

/// Parses `[ws][sign][0x]digits` in `base` (0 or 2..=36).
///
/// # Safety
/// `s` must be NUL-terminated.
unsafe fn scan_int(s: *const u8, base: u32) -> IntScan {
    // SAFETY: caller contract.
    let mut c = unsafe { Cursor::new(s) };
    while is_space(c.peek()) {
        c.bump();
    }
    let negative = match c.peek() {
        b'-' => {
            c.bump();
            true
        }
        b'+' => {
            c.bump();
            false
        }
        _ => false,
    };
    let mut base = base;
    if (base == 0 || base == 16)
        && c.peek() == b'0'
        && matches!(c.peek_at(1), b'x' | b'X')
        && digit(c.peek_at(2), 16).is_some()
    {
        c.pos += 2;
        base = 16;
    } else if base == 0 {
        base = if c.peek() == b'0' { 8 } else { 10 };
    }
    let mut magnitude: u64 = 0;
    let mut overflow = false;
    let mut digits = 0;
    while let Some(d) = digit(c.peek(), base) {
        c.bump();
        digits += 1;
        match magnitude
            .checked_mul(base as u64)
            .and_then(|m| m.checked_add(d as u64))
        {
            Some(m) => magnitude = m,
            None => overflow = true,
        }
    }
    IntScan {
        magnitude: if overflow { u64::MAX } else { magnitude },
        negative,
        overflow,
        end: if digits > 0 { c.pos } else { 0 },
    }
}

/// Value of ASCII digit `b` in `base`, if valid.
#[inline]
fn digit(b: u8, base: u32) -> Option<u32> {
    let v = match b {
        b'0'..=b'9' => (b - b'0') as u32,
        b'a'..=b'z' => (b - b'a') as u32 + 10,
        b'A'..=b'Z' => (b - b'A') as u32 + 10,
        _ => return None,
    };
    if v < base { Some(v) } else { None }
}

/// Stores the end pointer, if requested.
///
/// # Safety
/// `endptr` must be null or valid.
unsafe fn set_end(s: *const c_char, endptr: *mut *mut c_char, end: usize) {
    if !endptr.is_null() {
        // SAFETY: caller contract; `end` is within the string.
        unsafe { *endptr = s.add(end) as *mut c_char };
    }
}

/// Shared implementation of the signed conversions.
///
/// # Safety
/// `s` must be NUL-terminated; `endptr` null or valid.
unsafe fn strto_signed(
    s: *const c_char,
    endptr: *mut *mut c_char,
    base: c_int,
    min: i64,
    max: i64,
) -> i64 {
    if base != 0 && !(2..=36).contains(&base) {
        Errno::EINVAL.set();
        // SAFETY: forwarded.
        unsafe { set_end(s, endptr, 0) };
        return 0;
    }
    // SAFETY: forwarded.
    let scan = unsafe { scan_int(s as *const u8, base as u32) };
    // SAFETY: forwarded.
    unsafe { set_end(s, endptr, scan.end) };
    let limit = if scan.negative {
        min.unsigned_abs()
    } else {
        max as u64
    };
    if scan.overflow || scan.magnitude > limit {
        Errno::ERANGE.set();
        return if scan.negative { min } else { max };
    }
    if scan.negative {
        (scan.magnitude as i64).wrapping_neg()
    } else {
        scan.magnitude as i64
    }
}

/// Shared implementation of the unsigned conversions. As C requires, a
/// leading minus sign negates the value (modulo 2^N).
///
/// # Safety
/// `s` must be NUL-terminated; `endptr` null or valid.
unsafe fn strto_unsigned(s: *const c_char, endptr: *mut *mut c_char, base: c_int, max: u64) -> u64 {
    if base != 0 && !(2..=36).contains(&base) {
        Errno::EINVAL.set();
        // SAFETY: forwarded.
        unsafe { set_end(s, endptr, 0) };
        return 0;
    }
    // SAFETY: forwarded.
    let scan = unsafe { scan_int(s as *const u8, base as u32) };
    // SAFETY: forwarded.
    unsafe { set_end(s, endptr, scan.end) };
    if scan.overflow || scan.magnitude > max {
        Errno::ERANGE.set();
        return max;
    }
    if scan.negative {
        scan.magnitude.wrapping_neg() & max
    } else {
        scan.magnitude
    }
}

/// `strtol(3)`.
///
/// # Safety
/// `s` must be NUL-terminated; `endptr` null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strtol(s: *const c_char, endptr: *mut *mut c_char, base: c_int) -> c_long {
    // SAFETY: forwarded.
    unsafe { strto_signed(s, endptr, base, c_long::MIN, c_long::MAX) }
}

/// `strtoll(3)`.
///
/// # Safety
/// As for [`strtol`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strtoll(
    s: *const c_char,
    endptr: *mut *mut c_char,
    base: c_int,
) -> c_longlong {
    // SAFETY: forwarded.
    unsafe { strto_signed(s, endptr, base, c_longlong::MIN, c_longlong::MAX) }
}

/// `strtoimax(3)`.
///
/// # Safety
/// As for [`strtol`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strtoimax(s: *const c_char, endptr: *mut *mut c_char, base: c_int) -> i64 {
    // SAFETY: forwarded.
    unsafe { strto_signed(s, endptr, base, i64::MIN, i64::MAX) }
}

/// `strtoul(3)`.
///
/// # Safety
/// As for [`strtol`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strtoul(
    s: *const c_char,
    endptr: *mut *mut c_char,
    base: c_int,
) -> c_ulong {
    // SAFETY: forwarded.
    unsafe { strto_unsigned(s, endptr, base, c_ulong::MAX) }
}

/// `strtoull(3)`.
///
/// # Safety
/// As for [`strtol`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strtoull(
    s: *const c_char,
    endptr: *mut *mut c_char,
    base: c_int,
) -> c_ulonglong {
    // SAFETY: forwarded.
    unsafe { strto_unsigned(s, endptr, base, c_ulonglong::MAX) }
}

/// `strtoumax(3)`.
///
/// # Safety
/// As for [`strtol`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strtoumax(s: *const c_char, endptr: *mut *mut c_char, base: c_int) -> u64 {
    // SAFETY: forwarded.
    unsafe { strto_unsigned(s, endptr, base, u64::MAX) }
}

/// `atoi(3)`.
///
/// # Safety
/// `s` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn atoi(s: *const c_char) -> c_int {
    // SAFETY: forwarded.
    unsafe { strtol(s, ptr::null_mut(), 10) as c_int }
}

/// `atol(3)`.
///
/// # Safety
/// `s` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn atol(s: *const c_char) -> c_long {
    // SAFETY: forwarded.
    unsafe { strtol(s, ptr::null_mut(), 10) }
}

/// `atoll(3)`.
///
/// # Safety
/// `s` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn atoll(s: *const c_char) -> c_longlong {
    // SAFETY: forwarded.
    unsafe { strtoll(s, ptr::null_mut(), 10) }
}

/// `atof(3)`.
///
/// # Safety
/// `s` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn atof(s: *const c_char) -> f64 {
    // SAFETY: forwarded.
    unsafe { strtod(s, ptr::null_mut()) }
}

// ---------------------------------------------------------------------
// Floating point.

/// Result of scanning a floating-point number.
pub struct FloatScan {
    /// The value as an `f64`.
    pub value: f64,
    /// Bytes consumed (0 if no number was found).
    pub end: usize,
    /// `ERANGE` should be reported (overflow or underflow).
    pub range_error: bool,
}

/// Parses the longest floating-point prefix of `s` (C `strtod` syntax).
/// `f32` selects single-precision rounding for the decimal path.
///
/// # Safety
/// `s` must be NUL-terminated.
pub unsafe fn scan_float(s: *const u8, single: bool) -> FloatScan {
    // SAFETY: caller contract.
    let mut c = unsafe { Cursor::new(s) };
    while is_space(c.peek()) {
        c.bump();
    }
    let negative = match c.peek() {
        b'-' => {
            c.bump();
            true
        }
        b'+' => {
            c.bump();
            false
        }
        _ => false,
    };
    let sign = if negative { -1.0 } else { 1.0 };
    let none = FloatScan {
        value: 0.0,
        end: 0,
        range_error: false,
    };

    // Infinity and NaN.
    if c.eat_ci(b"inf") {
        c.eat_ci(b"inity");
        return FloatScan {
            value: sign * f64::INFINITY,
            end: c.pos,
            range_error: false,
        };
    }
    if c.eat_ci(b"nan") {
        // Optional "(n-char-sequence)".
        if c.peek() == b'(' {
            let mut i = 1;
            while c.peek_at(i).is_ascii_alphanumeric() || c.peek_at(i) == b'_' {
                i += 1;
            }
            if c.peek_at(i) == b')' {
                c.pos += i + 1;
            }
        }
        return FloatScan {
            value: sign * f64::NAN,
            end: c.pos,
            range_error: false,
        };
    }

    // Hexadecimal.
    if c.peek() == b'0'
        && matches!(c.peek_at(1), b'x' | b'X')
        && (digit(c.peek_at(2), 16).is_some()
            || (c.peek_at(2) == b'.' && digit(c.peek_at(3), 16).is_some()))
    {
        c.pos += 2;
        return scan_hex_float(&mut c, sign);
    }

    // Decimal: digits [. digits] [e [sign] digits]; at least one digit.
    let start = c.pos;
    let mut digits = 0usize;
    let mut nonzero = false;
    while c.peek().is_ascii_digit() {
        nonzero |= c.bump() != b'0';
        digits += 1;
    }
    if c.peek() == b'.' {
        c.bump();
        while c.peek().is_ascii_digit() {
            nonzero |= c.bump() != b'0';
            digits += 1;
        }
    }
    if digits == 0 {
        return none;
    }
    if matches!(c.peek(), b'e' | b'E') {
        let save = c.pos;
        c.bump();
        if matches!(c.peek(), b'+' | b'-') {
            c.bump();
        }
        if c.peek().is_ascii_digit() {
            while c.peek().is_ascii_digit() {
                c.bump();
            }
        } else {
            c.pos = save;
        }
    }
    // SAFETY: `[start, pos)` is ASCII within the string.
    let text = unsafe {
        core::str::from_utf8_unchecked(core::slice::from_raw_parts(s.add(start), c.pos - start))
    };
    let value = if single {
        text.parse::<f32>().map(f64::from)
    } else {
        text.parse::<f64>()
    }
    .unwrap_or(0.0);
    let range_error = value.is_infinite() || (nonzero && (value == 0.0 || value.is_subnormal()));
    FloatScan {
        value: sign * value,
        end: c.pos,
        range_error,
    }
}

/// Parses the mantissa and exponent of a hexadecimal float (after "0x").
fn scan_hex_float(c: &mut Cursor, sign: f64) -> FloatScan {
    let mut mant: u64 = 0;
    let mut sticky = false;
    let mut exp: i64 = 0; // binary exponent adjustment from digit position
    let mut any = false;
    let mut nonzero = false;
    let mut after_point = false;
    loop {
        let b = c.peek();
        if let Some(d) = digit(b, 16) {
            any = true;
            nonzero |= d != 0;
            if mant >> 60 == 0 {
                mant = (mant << 4) | d as u64;
                if after_point {
                    exp -= 4;
                }
            } else {
                // Too many digits for 64 bits: keep a sticky bit and
                // account for the position.
                sticky |= d != 0;
                if !after_point {
                    exp += 4;
                }
            }
        } else if b == b'.' && !after_point {
            after_point = true;
        } else {
            break;
        }
        c.bump();
    }
    if !any {
        return FloatScan {
            value: 0.0,
            end: 0,
            range_error: false,
        };
    }
    if matches!(c.peek(), b'p' | b'P') {
        let save = c.pos;
        c.bump();
        let neg = match c.peek() {
            b'-' => {
                c.bump();
                true
            }
            b'+' => {
                c.bump();
                false
            }
            _ => false,
        };
        if c.peek().is_ascii_digit() {
            let mut e: i64 = 0;
            while c.peek().is_ascii_digit() {
                e = e
                    .saturating_mul(10)
                    .saturating_add((c.bump() - b'0') as i64);
            }
            exp = exp.saturating_add(if neg { -e } else { e });
        } else {
            c.pos = save;
        }
    }
    let value = hex_to_f64(mant, sticky, exp);
    let range_error = value.is_infinite() || (nonzero && (value == 0.0 || value.is_subnormal()));
    FloatScan {
        value: sign * value,
        end: c.pos,
        range_error,
    }
}

/// Computes `mant * 2^exp` rounded to nearest even, where `sticky` means
/// non-zero bits were dropped below `mant`.
fn hex_to_f64(mant: u64, sticky: bool, exp: i64) -> f64 {
    if mant == 0 {
        return 0.0;
    }
    // Normalise so the top bit of the mantissa is bit 63.
    let shift = mant.leading_zeros();
    let m = mant << shift;
    // The value is m * 2^(exp - shift - 63) with m in [2^63, 2^64).
    let e = exp - shift as i64 + 63; // exponent of the leading bit
    if e > 1023 {
        return f64::INFINITY;
    }
    // Number of mantissa bits we can keep (53 for normal numbers, fewer
    // for subnormals).
    let keep: i64 = if e >= -1022 { 53 } else { 53 - (-1022 - e) };
    if keep <= 0 {
        // Below half the smallest subnormal: rounds to zero unless it is
        // exactly half and sticky/odd... it can only round up to the
        // smallest subnormal when keep == 0 and the value exceeds half.
        if keep == 0 && (m > 1 << 63 || sticky) {
            return f64::from_bits(1);
        }
        return 0.0;
    }
    let drop = 64 - keep as u32;
    let mut kept = m >> drop;
    let rem = m & ((1u64 << drop) - 1);
    let half = 1u64 << (drop - 1);
    if rem > half || (rem == half && (sticky || kept & 1 == 1)) {
        kept += 1;
    } else if rem == half && !sticky && kept & 1 == 0 {
        // exactly half, even: keep
    }
    // Rounding may have carried into a new bit.
    let mut e = e;
    if kept >> keep == 1 {
        kept >>= 1;
        e += 1;
        if e > 1023 {
            return f64::INFINITY;
        }
    }
    if e >= -1022 {
        let biased = (e + 1023) as u64;
        f64::from_bits((biased << 52) | (kept & ((1 << 52) - 1)))
    } else {
        // Subnormal: `kept` already has the right number of bits.
        f64::from_bits(kept)
    }
}

/// `strtod(3)`.
///
/// # Safety
/// `s` must be NUL-terminated; `endptr` null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strtod(s: *const c_char, endptr: *mut *mut c_char) -> f64 {
    // SAFETY: forwarded.
    let r = unsafe { scan_float(s as *const u8, false) };
    // SAFETY: forwarded.
    unsafe { set_end(s, endptr, r.end) };
    if r.range_error {
        Errno::ERANGE.set();
    }
    r.value
}

/// `strtof(3)`.
///
/// # Safety
/// As for [`strtod`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strtof(s: *const c_char, endptr: *mut *mut c_char) -> f32 {
    // SAFETY: forwarded.
    let r = unsafe { scan_float(s as *const u8, true) };
    // SAFETY: forwarded.
    unsafe { set_end(s, endptr, r.end) };
    let v = r.value as f32;
    if r.range_error || (v.is_infinite() && r.value.is_finite()) || (v == 0.0 && r.value != 0.0) {
        Errno::ERANGE.set();
    }
    v
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;

    fn cs(s: &str) -> CString {
        CString::new(s).unwrap()
    }

    fn l(s: &str, base: c_int) -> (c_long, usize) {
        let c = cs(s);
        let mut end = ptr::null_mut();
        // SAFETY: NUL-terminated.
        let v = unsafe { strtol(c.as_ptr(), &mut end, base) };
        (v, end as usize - c.as_ptr() as usize)
    }

    fn ul(s: &str, base: c_int) -> (c_ulong, usize) {
        let c = cs(s);
        let mut end = ptr::null_mut();
        // SAFETY: NUL-terminated.
        let v = unsafe { strtoul(c.as_ptr(), &mut end, base) };
        (v, end as usize - c.as_ptr() as usize)
    }

    fn d(s: &str) -> (f64, usize) {
        let c = cs(s);
        let mut end = ptr::null_mut();
        // SAFETY: NUL-terminated.
        let v = unsafe { strtod(c.as_ptr(), &mut end) };
        (v, end as usize - c.as_ptr() as usize)
    }

    #[test]
    fn integers() {
        assert_eq!(l("  42xyz", 10), (42, 4));
        assert_eq!(l("-42", 10), (-42, 3));
        assert_eq!(l("+42", 0), (42, 3));
        assert_eq!(l("0x1fZ", 16), (31, 4));
        assert_eq!(l("0x1f", 0), (31, 4));
        assert_eq!(l("0xg", 16), (0, 1));
        assert_eq!(l("0x", 0), (0, 1));
        assert_eq!(l("017", 0), (15, 3));
        assert_eq!(l("017", 10), (17, 3));
        assert_eq!(l("zz", 36), (35 * 36 + 35, 2));
        assert_eq!(l("abc", 10), (0, 0));
        assert_eq!(l("", 10), (0, 0));
        assert_eq!(l("-", 10), (0, 0));
        assert_eq!(l("  ", 10), (0, 0));
        Errno(0).set();
        assert_eq!(l("9223372036854775807", 10), (c_long::MAX, 19));
        assert_eq!(Errno::get(), Errno(0));
        assert_eq!(l("9223372036854775808", 10), (c_long::MAX, 19));
        assert_eq!(Errno::get(), Errno::ERANGE);
        Errno(0).set();
        assert_eq!(l("-9223372036854775808", 10), (c_long::MIN, 20));
        assert_eq!(Errno::get(), Errno(0));
        assert_eq!(l("-9223372036854775809", 10), (c_long::MIN, 20));
        assert_eq!(Errno::get(), Errno::ERANGE);
        Errno(0).set();
        assert_eq!(l("99999999999999999999999999999", 10), (c_long::MAX, 29));
        assert_eq!(Errno::get(), Errno::ERANGE);
        Errno(0).set();
        assert_eq!(l("5", 1), (0, 0));
        assert_eq!(Errno::get(), Errno::EINVAL);
        assert_eq!(l("5", 37), (0, 0));
        assert_eq!(ul("-1", 10), (c_ulong::MAX, 2));
        assert_eq!(ul("18446744073709551615", 10), (c_ulong::MAX, 20));
        Errno(0).set();
        assert_eq!(ul("18446744073709551616", 10), (c_ulong::MAX, 20));
        assert_eq!(Errno::get(), Errno::ERANGE);
        // SAFETY: NUL-terminated literals.
        unsafe {
            assert_eq!(atoi(cs("  -17 apples").as_ptr()), -17);
            assert_eq!(atoi(cs("99999999999").as_ptr()), 99999999999i64 as c_int);
            assert_eq!(atol(cs("123456789012").as_ptr()), 123456789012);
            assert_eq!(atoll(cs("-5").as_ptr()), -5);
        }
    }

    #[test]
    fn decimals() {
        assert_eq!(d("1.5"), (1.5, 3));
        assert_eq!(d("  -2.5e3xyz"), (-2500.0, 8));
        assert_eq!(d("1e"), (1.0, 1));
        assert_eq!(d("1e+"), (1.0, 1));
        assert_eq!(d("1E2"), (100.0, 3));
        assert_eq!(d(".5"), (0.5, 2));
        assert_eq!(d("5."), (5.0, 2));
        assert_eq!(d("."), (0.0, 0));
        assert_eq!(d("e5"), (0.0, 0));
        assert_eq!(d("-"), (0.0, 0));
        assert_eq!(d("0.1"), (0.1, 3));
        assert_eq!(
            d("3.14159265358979323846264338327950288"),
            (core::f64::consts::PI, 37)
        );
        assert_eq!(d("2.2250738585072011e-308"), (2.2250738585072011e-308, 23));
        assert_eq!(d("1.7976931348623157e308"), (f64::MAX, 22));
        let (v, n) = d("inf");
        assert!(v.is_infinite() && v > 0.0 && n == 3);
        let (v, n) = d("-INFINITY!");
        assert!(v.is_infinite() && v < 0.0 && n == 9);
        let (v, n) = d("infinit");
        assert!(v.is_infinite() && n == 3);
        let (v, n) = d("nan");
        assert!(v.is_nan() && n == 3);
        let (v, n) = d("NaN(abc_1)x");
        assert!(v.is_nan() && n == 10);
        let (v, n) = d("nan(abc");
        assert!(v.is_nan() && n == 3);
        // Signed zero and negative NaN sign.
        assert!(d("-0").0.is_sign_negative());
        Errno(0).set();
        let (v, _) = d("1e400");
        assert!(v.is_infinite());
        assert_eq!(Errno::get(), Errno::ERANGE);
        Errno(0).set();
        let (v, _) = d("1e-400");
        assert_eq!(v, 0.0);
        assert_eq!(Errno::get(), Errno::ERANGE);
        Errno(0).set();
        assert_eq!(d("0e-400"), (0.0, 6));
        assert_eq!(Errno::get(), Errno(0));
        let (v, _) = d("4.9e-324");
        assert_eq!(v, f64::from_bits(1));
        assert_eq!(Errno::get(), Errno::ERANGE);
        let c = cs("3.4028236e38");
        // SAFETY: NUL-terminated.
        let f = unsafe { strtof(c.as_ptr(), ptr::null_mut()) };
        assert!(f.is_infinite());
        let c = cs("0.1");
        // SAFETY: NUL-terminated.
        let f = unsafe { strtof(c.as_ptr(), ptr::null_mut()) };
        assert_eq!(f, 0.1f32);
        // Round-to-nearest for f32 must not double round through f64.
        let c = cs("1.000000178813934326171875001");
        // SAFETY: NUL-terminated.
        let f = unsafe { strtof(c.as_ptr(), ptr::null_mut()) };
        assert_eq!(f.to_bits(), 0x3f800002);
    }

    #[test]
    fn hex_floats() {
        assert_eq!(d("0x1p0"), (1.0, 5));
        assert_eq!(d("0x1.8p1"), (3.0, 7));
        assert_eq!(d("0x.8"), (0.5, 4));
        assert_eq!(d("0x1p-1"), (0.5, 6));
        assert_eq!(d("0xAp"), (10.0, 3));
        assert_eq!(d("0x"), (0.0, 1));
        assert_eq!(d("0x1.fffffffffffffp1023"), (f64::MAX, 22));
        assert_eq!(d("0x1p1024").0, f64::INFINITY);
        assert_eq!(d("0x1p-1074"), (f64::from_bits(1), 9));
        assert_eq!(d("0x1p-1075"), (0.0, 9));
        assert_eq!(d("0x1.8p-1075"), (f64::from_bits(1), 11));
        assert_eq!(d("0x1p-1022"), (f64::MIN_POSITIVE, 9));
        // Round half to even on the 53-bit boundary.
        assert_eq!(d("0x1.00000000000008p0").0, 1.0);
        assert_eq!(d("0x1.00000000000018p0").0, 1.0 + 2.0 * f64::EPSILON);
        assert_eq!(d("0x1.000000000000081p0").0, 1.0 + f64::EPSILON);
        // Many digits: sticky handling.
        assert_eq!(d("0x1.0000000000000000000000001p0").0, 1.0);
        assert_eq!(
            d("0x123456789abcdef0123456789p0").0,
            0x123456789abcdef0123456789u128 as f64
        );
        assert_eq!(d("-0x1p2"), (-4.0, 6));
    }

    #[test]
    fn division() {
        use super::super::{abs, div, ldiv, llabs};
        let r = div(7, -2);
        assert_eq!((r.quot, r.rem), (-3, 1));
        let r = ldiv(-7, 2);
        assert_eq!((r.quot, r.rem), (-3, -1));
        assert_eq!(abs(-5), 5);
        assert_eq!(abs(c_int::MIN), c_int::MIN);
        assert_eq!(llabs(-5), 5);
    }
}
