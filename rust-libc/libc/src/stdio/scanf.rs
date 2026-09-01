//! The `scanf` family.
//!
//! [`scan`] reads from a [`Source`] with single-byte pushback, exactly
//! the capability C guarantees (`ungetc` of one character). Numbers are
//! collected into a small buffer using a prefix-validity check, then
//! converted with the `strtol`/`strtod` machinery.

use super::{File, lock, stdin};
use crate::arch::va::VaList;
use crate::c_char;
use crate::errno::Errno;
use crate::stdlib::num;
use core::ffi::{c_int, c_void};

/// Input for [`scan`].
pub trait Source {
    /// Next byte, or `None` at end of input / on error.
    fn next(&mut self) -> Option<u8>;
    /// Pushes back the byte most recently returned by `next`.
    fn unget(&mut self, b: u8);
}

impl Source for File {
    fn next(&mut self) -> Option<u8> {
        self.getc()
    }
    fn unget(&mut self, b: u8) {
        self.ungetc(b);
    }
}

/// A NUL-terminated string source.
pub struct StrSource {
    p: *const u8,
    pos: usize,
}

impl Source for StrSource {
    fn next(&mut self) -> Option<u8> {
        // SAFETY: never reads past the terminator.
        let b = unsafe { *self.p.add(self.pos) };
        if b == 0 {
            None
        } else {
            self.pos += 1;
            Some(b)
        }
    }
    fn unget(&mut self, _b: u8) {
        self.pos -= 1;
    }
}

/// Reader with position tracking and one-byte pushback on top of a
/// [`Source`].
struct Reader<'a, S: Source> {
    src: &'a mut S,
    consumed: usize,
    /// Set once `next` hit end of input.
    eof: bool,
}

impl<S: Source> Reader<'_, S> {
    fn next(&mut self) -> Option<u8> {
        match self.src.next() {
            Some(b) => {
                self.consumed += 1;
                Some(b)
            }
            None => {
                self.eof = true;
                None
            }
        }
    }

    fn unget(&mut self, b: u8) {
        self.consumed -= 1;
        self.src.unget(b);
    }

    fn skip_space(&mut self) {
        while let Some(b) = self.next() {
            if !is_space(b) {
                self.unget(b);
                return;
            }
        }
    }
}

fn is_space(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r')
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Length {
    None,
    Hh,
    H,
    L,
    Ll,
    J,
    Z,
    T,
    BigL,
}

/// Stores an integer result according to the length modifier.
///
/// # Safety
/// `dst` must point to an integer of the modifier's size.
unsafe fn store_int(dst: *mut c_void, length: Length, v: u64) {
    // SAFETY: caller contract.
    unsafe {
        match length {
            Length::Hh => *(dst as *mut u8) = v as u8,
            Length::H => *(dst as *mut u16) = v as u16,
            Length::None => *(dst as *mut u32) = v as u32,
            _ => *(dst as *mut u64) = v,
        }
    }
}

/// Whether appending `c` to the number text `buf` keeps it a prefix of
/// some valid floating-point literal.
fn float_accepts(buf: &[u8], c: u8) -> bool {
    let body = match buf.first() {
        Some(b'+' | b'-') => &buf[1..],
        _ => buf,
    };
    if body.is_empty() {
        return matches!(
            c,
            b'+' | b'-' | b'0'..=b'9' | b'.' | b'i' | b'I' | b'n' | b'N'
        ) && !(buf.len() == 1 && matches!(c, b'+' | b'-'));
    }
    let lower = |b: u8| b.to_ascii_lowercase();
    if matches!(lower(body[0]), b'i' | b'n') {
        let word: &[u8] = if lower(body[0]) == b'i' {
            b"infinity"
        } else {
            b"nan"
        };
        return body.len() < word.len()
            && lower(c) == word[body.len()]
            && body.iter().zip(word).all(|(a, b)| lower(*a) == *b);
    }
    let hex = body.len() >= 2 && body[0] == b'0' && matches!(body[1], b'x' | b'X');
    let digits: &[u8] = if hex { &body[2..] } else { body };
    let exp_char = |b: u8| {
        if hex {
            matches!(b, b'p' | b'P')
        } else {
            matches!(b, b'e' | b'E')
        }
    };
    let is_digit = |b: u8| {
        if hex {
            b.is_ascii_hexdigit()
        } else {
            b.is_ascii_digit()
        }
    };
    let exp_pos = digits.iter().position(|&b| exp_char(b));
    match exp_pos {
        None => {
            if !hex && body.len() == 1 && body[0] == b'0' && matches!(c, b'x' | b'X') {
                return true;
            }
            let seen_digit = digits.iter().any(|&b| is_digit(b));
            let seen_point = digits.contains(&b'.');
            is_digit(c) || (c == b'.' && !seen_point) || (exp_char(c) && seen_digit)
        }
        Some(e) => {
            // After the exponent letter: an optional sign, then digits.
            let exp = &digits[e + 1..];
            (exp.is_empty() && matches!(c, b'+' | b'-')) || c.is_ascii_digit()
        }
    }
}

/// Whether appending `c` to `buf` keeps it a prefix of an integer in
/// `base` (0 meaning C's auto-detection).
fn int_accepts(buf: &[u8], c: u8, base: u32) -> bool {
    let body = match buf.first() {
        Some(b'+' | b'-') => &buf[1..],
        _ => buf,
    };
    if body.is_empty() {
        return matches!(c, b'+' | b'-') && buf.is_empty()
            || digit_of(c, if base == 0 { 10 } else { base }).is_some();
    }
    if (base == 16 || base == 0) && body.len() == 1 && body[0] == b'0' && matches!(c, b'x' | b'X') {
        return true;
    }
    let effective = if base != 0 {
        base
    } else if body.len() >= 2 && body[0] == b'0' && matches!(body[1], b'x' | b'X') {
        16
    } else if body[0] == b'0' {
        8
    } else {
        10
    };
    if effective == 16 && body.len() == 2 && body[0] == b'0' && matches!(body[1], b'x' | b'X') {
        return c.is_ascii_hexdigit();
    }
    digit_of(c, effective).is_some()
}

fn digit_of(c: u8, base: u32) -> Option<u32> {
    let v = match c {
        b'0'..=b'9' => (c - b'0') as u32,
        b'a'..=b'z' => (c - b'a') as u32 + 10,
        b'A'..=b'Z' => (c - b'A') as u32 + 10,
        _ => return None,
    };
    (v < base).then_some(v)
}

/// Collects up to `width` bytes while `accept` says the text is still a
/// valid prefix. Pushes back the first rejected byte.
fn collect<S: Source>(
    r: &mut Reader<'_, S>,
    width: usize,
    buf: &mut [u8; 128],
    accept: impl Fn(&[u8], u8) -> bool,
) -> usize {
    let mut n = 0;
    while n < width {
        let Some(b) = r.next() else { break };
        if n < buf.len() - 1 && accept(&buf[..n], b) {
            buf[n] = b;
            n += 1;
        } else {
            r.unget(b);
            break;
        }
    }
    n
}

/// A 256-bit scanset for `%[`.
struct Set([u64; 4], bool);

impl Set {
    fn contains(&self, b: u8) -> bool {
        (self.0[(b >> 6) as usize] & (1 << (b & 63)) != 0) != self.1
    }
}

/// Parses a `%[...]` scanset starting after the `[`. Returns the set and
/// the position after the closing `]`.
///
/// # Safety
/// `p` must point into a NUL-terminated format.
unsafe fn parse_set(mut p: *const u8) -> Option<(Set, *const u8)> {
    let mut set = Set([0; 4], false);
    // SAFETY: all reads stop at NUL.
    unsafe {
        if *p == b'^' {
            set.1 = true;
            p = p.add(1);
        }
        let mut first = true;
        loop {
            let c = *p;
            if c == 0 {
                return None;
            }
            if c == b']' && !first {
                return Some((set, p.add(1)));
            }
            first = false;
            let mut hi = c;
            if *p.add(1) == b'-' && *p.add(2) != b']' && *p.add(2) != 0 && *p.add(2) >= c {
                hi = *p.add(2);
                p = p.add(2);
            }
            for b in c..=hi {
                set.0[(b >> 6) as usize] |= 1 << (b & 63);
            }
            p = p.add(1);
        }
    }
}

/// Decodes one UTF-8 sequence whose first byte is `first`, reading the
/// continuation bytes from `r`. Returns `None` on malformed input.
fn decode_utf8<S: Source>(r: &mut Reader<'_, S>, first: u8) -> Option<u32> {
    let (len, init) = match first {
        0x00..=0x7f => return Some(first as u32),
        0xc2..=0xdf => (1, (first & 0x1f) as u32),
        0xe0..=0xef => (2, (first & 0x0f) as u32),
        0xf0..=0xf4 => (3, (first & 0x07) as u32),
        _ => return None,
    };
    let mut cp = init;
    for _ in 0..len {
        let b = r.next()?;
        if b & 0xc0 != 0x80 {
            r.unget(b);
            return None;
        }
        cp = (cp << 6) | (b & 0x3f) as u32;
    }
    char::from_u32(cp).map(|c| c as u32)
}

/// Runs the format `fmt` over `src`, storing into the `va_list`.
/// Returns the number of assignments, or `EOF` on input failure before
/// the first conversion.
///
/// # Safety
/// `fmt` must be NUL-terminated and the arguments must match it.
pub unsafe fn scan<S: Source>(src: &mut S, fmt: *const u8, ap: &mut VaList) -> c_int {
    let mut r = Reader {
        src,
        consumed: 0,
        eof: false,
    };
    let mut assigned: c_int = 0;
    let mut p = fmt;
    let mut buf = [0u8; 128];
    // SAFETY: the format is NUL-terminated; every read stops at NUL.
    unsafe {
        loop {
            let c = *p;
            if c == 0 {
                break;
            }
            if is_space(c) {
                r.skip_space();
                p = p.add(1);
                continue;
            }
            if c != b'%' {
                match r.next() {
                    Some(b) if b == c => {}
                    Some(b) => {
                        r.unget(b);
                        break;
                    }
                    None => return if assigned == 0 { super::EOF } else { assigned },
                }
                p = p.add(1);
                continue;
            }
            p = p.add(1);
            if *p == b'%' {
                r.skip_space();
                match r.next() {
                    Some(b'%') => {}
                    Some(b) => {
                        r.unget(b);
                        break;
                    }
                    None => return if assigned == 0 { super::EOF } else { assigned },
                }
                p = p.add(1);
                continue;
            }
            let suppress = *p == b'*';
            if suppress {
                p = p.add(1);
            }
            let mut width = 0usize;
            while (*p).is_ascii_digit() {
                width = width
                    .saturating_mul(10)
                    .saturating_add((*p - b'0') as usize);
                p = p.add(1);
            }
            let width = if width == 0 { usize::MAX } else { width };
            let length = match *p {
                b'h' => {
                    p = p.add(1);
                    if *p == b'h' {
                        p = p.add(1);
                        Length::Hh
                    } else {
                        Length::H
                    }
                }
                b'l' => {
                    p = p.add(1);
                    if *p == b'l' {
                        p = p.add(1);
                        Length::Ll
                    } else {
                        Length::L
                    }
                }
                b'j' => {
                    p = p.add(1);
                    Length::J
                }
                b'z' => {
                    p = p.add(1);
                    Length::Z
                }
                b't' => {
                    p = p.add(1);
                    Length::T
                }
                b'L' | b'q' => {
                    p = p.add(1);
                    Length::BigL
                }
                _ => Length::None,
            };
            let conv = *p;
            p = p.add(1);
            let dst = if suppress || conv == 0 {
                core::ptr::null_mut()
            } else {
                ap.ptr()
            };
            match conv {
                b'd' | b'i' | b'u' | b'o' | b'x' | b'X' | b'p' => {
                    let base = match conv {
                        b'd' | b'u' => 10,
                        b'i' => 0,
                        b'o' => 8,
                        _ => 16,
                    };
                    r.skip_space();
                    if r.eof {
                        return if assigned == 0 { super::EOF } else { assigned };
                    }
                    let n = collect(&mut r, width, &mut buf, |b, c| int_accepts(b, c, base));
                    buf[n] = 0;
                    let mut end: *mut c_char = core::ptr::null_mut();
                    let value = if matches!(conv, b'd' | b'i') {
                        num::strtoll(buf.as_ptr() as *const c_char, &mut end, base as c_int) as u64
                    } else {
                        num::strtoull(buf.as_ptr() as *const c_char, &mut end, base as c_int)
                    };
                    if end as *const u8 == buf.as_ptr() {
                        break; // matching failure
                    }
                    if !dst.is_null() {
                        if conv == b'p' {
                            *(dst as *mut u64) = value;
                        } else {
                            store_int(dst, length, value);
                        }
                        assigned += 1;
                    }
                }
                b'a' | b'A' | b'e' | b'E' | b'f' | b'F' | b'g' | b'G' => {
                    r.skip_space();
                    if r.eof {
                        return if assigned == 0 { super::EOF } else { assigned };
                    }
                    let n = collect(&mut r, width, &mut buf, float_accepts);
                    buf[n] = 0;
                    let res = num::scan_float(buf.as_ptr(), length == Length::None);
                    if res.end == 0 {
                        break;
                    }
                    if !dst.is_null() {
                        match length {
                            Length::None => *(dst as *mut f32) = res.value as f32,
                            Length::BigL => {
                                let (m, se) = crate::arch::va::f64_to_x87(res.value);
                                *(dst as *mut u64) = m;
                                *((dst as *mut u8).add(8) as *mut u16) = se;
                            }
                            _ => *(dst as *mut f64) = res.value,
                        }
                        assigned += 1;
                    }
                }
                b's' | b'c' | b'[' => {
                    let set = if conv == b'[' {
                        match parse_set(p) {
                            Some((set, next)) => {
                                p = next;
                                Some(set)
                            }
                            None => {
                                Errno::EINVAL.set();
                                return -1;
                            }
                        }
                    } else {
                        None
                    };
                    if conv != b'c' {
                        r.skip_space();
                    }
                    if r.eof {
                        return if assigned == 0 { super::EOF } else { assigned };
                    }
                    let width = if conv == b'c' && width == usize::MAX {
                        1
                    } else {
                        width
                    };
                    let wide = length == Length::L;
                    let mut n = 0usize;
                    let mut out = dst as *mut u8;
                    while n < width {
                        let Some(b) = r.next() else { break };
                        let accept = match &set {
                            Some(set) => set.contains(b),
                            None => conv == b'c' || !is_space(b),
                        };
                        if !accept {
                            r.unget(b);
                            break;
                        }
                        if wide {
                            let Some(cp) = decode_utf8(&mut r, b) else {
                                Errno::EILSEQ.set();
                                return if assigned == 0 { -1 } else { assigned };
                            };
                            if !out.is_null() {
                                *(out as *mut u32) = cp;
                                out = out.add(4);
                            }
                        } else if !out.is_null() {
                            *out = b;
                            out = out.add(1);
                        }
                        n += 1;
                    }
                    if n == 0 {
                        break;
                    }
                    if !dst.is_null() {
                        if conv != b'c' {
                            if wide {
                                *(out as *mut u32) = 0;
                            } else {
                                *out = 0;
                            }
                        }
                        assigned += 1;
                    }
                }
                b'n' => {
                    if !dst.is_null() {
                        store_int(dst, length, r.consumed as u64);
                    }
                }
                _ => {
                    Errno::EINVAL.set();
                    return -1;
                }
            }
        }
    }
    if r.eof && assigned == 0 && r.consumed == 0 {
        super::EOF
    } else {
        assigned
    }
}

/// `vfscanf(3)`.
///
/// # Safety
/// `f` must be a valid stream; `fmt` NUL-terminated with matching args.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vfscanf(f: *mut File, fmt: *const c_char, ap: *mut VaList) -> c_int {
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    // SAFETY: forwarded.
    unsafe { scan(&mut *g, fmt as *const u8, &mut *ap) }
}

/// `vscanf(3)`.
///
/// # Safety
/// `fmt` must be NUL-terminated with matching args.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vscanf(fmt: *const c_char, ap: *mut VaList) -> c_int {
    // SAFETY: forwarded; stdin is always valid.
    unsafe { vfscanf(stdin, fmt, ap) }
}

/// `vsscanf(3)`.
///
/// # Safety
/// `s` and `fmt` must be NUL-terminated; args must match.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vsscanf(s: *const c_char, fmt: *const c_char, ap: *mut VaList) -> c_int {
    let mut src = StrSource {
        p: s as *const u8,
        pos: 0,
    };
    // SAFETY: forwarded.
    unsafe { scan(&mut src, fmt as *const u8, &mut *ap) }
}

#[cfg(not(test))]
mod stubs {
    use crate::arch::va::variadic_stub;
    variadic_stub!(scanf, 1, "rsi", super::vscanf);
    variadic_stub!(fscanf, 2, "rdx", super::vfscanf);
    variadic_stub!(sscanf, 2, "rdx", super::vsscanf);
}

#[cfg(test)]
mod tests {
    use super::*;

    struct FakeArgs {
        words: Vec<u64>,
    }

    impl FakeArgs {
        fn list(&mut self) -> VaList {
            // SAFETY: documented VaList layout; register areas exhausted.
            unsafe {
                core::mem::transmute::<[u64; 3], VaList>([
                    (6 * 8) as u64 | ((6 * 8 + 8 * 16) as u64) << 32,
                    self.words.as_mut_ptr() as u64,
                    0,
                ])
            }
        }
    }

    fn run(input: &str, fmt: &str, ptrs: Vec<u64>) -> c_int {
        let cin = std::ffi::CString::new(input).unwrap();
        let cfmt = std::ffi::CString::new(fmt).unwrap();
        let mut args = FakeArgs { words: ptrs };
        // SAFETY: the pointers match the format.
        unsafe { vsscanf(cin.as_ptr(), cfmt.as_ptr(), &mut args.list()) }
    }

    #[test]
    fn integers_and_strings() {
        let (mut a, mut b, mut c) = (0i32, 0i32, 0u32);
        assert_eq!(
            run(
                "12 -34 0x1f",
                "%d %d %x",
                vec![
                    &mut a as *mut i32 as u64,
                    &mut b as *mut i32 as u64,
                    &mut c as *mut u32 as u64
                ]
            ),
            3
        );
        assert_eq!((a, b, c), (12, -34, 31));
        let mut l = 0i64;
        let mut h = 0i16;
        let mut hh = 0i8;
        assert_eq!(
            run(
                "123456789012 7 -3",
                "%ld %hd %hhd",
                vec![
                    &mut l as *mut i64 as u64,
                    &mut h as *mut i16 as u64,
                    &mut hh as *mut i8 as u64
                ]
            ),
            3
        );
        assert_eq!((l, h, hh), (123456789012, 7, -3));
        assert_eq!(
            run(
                "010 0x10 10",
                "%i %i %i",
                vec![
                    &mut a as *mut i32 as u64,
                    &mut b as *mut i32 as u64,
                    &mut c as *mut u32 as u64
                ]
            ),
            3
        );
        assert_eq!((a, b, c), (8, 16, 10));
        let mut s = [0u8; 16];
        let mut t = [0u8; 16];
        assert_eq!(
            run(
                "  hello world",
                "%s %3s",
                vec![s.as_mut_ptr() as u64, t.as_mut_ptr() as u64]
            ),
            2
        );
        assert_eq!(&s[..6], b"hello\0");
        assert_eq!(&t[..4], b"wor\0");
        let mut ch = [0u8; 3];
        assert_eq!(run("ab", "%2c", vec![ch.as_mut_ptr() as u64]), 1);
        assert_eq!(&ch, b"ab\0");
        assert_eq!(
            run(
                "abc123",
                "%[a-c]%d",
                vec![s.as_mut_ptr() as u64, &mut a as *mut i32 as u64]
            ),
            2
        );
        assert_eq!(&s[..4], b"abc\0");
        assert_eq!(a, 123);
        assert_eq!(run("hello]x", "%[^]]", vec![s.as_mut_ptr() as u64]), 1);
        assert_eq!(&s[..6], b"hello\0");
        assert_eq!(run("]]]x", "%[]]", vec![s.as_mut_ptr() as u64]), 1);
        assert_eq!(&s[..4], b"]]]\0");
    }

    #[test]
    fn floats_and_misc() {
        let (mut f, mut d) = (0f32, 0f64);
        assert_eq!(
            run(
                "1.5 -2.5e3",
                "%f %lf",
                vec![&mut f as *mut f32 as u64, &mut d as *mut f64 as u64]
            ),
            2
        );
        assert_eq!((f, d), (1.5, -2500.0));
        assert_eq!(
            run(
                "inf nan",
                "%f %lf",
                vec![&mut f as *mut f32 as u64, &mut d as *mut f64 as u64]
            ),
            2
        );
        assert!(f.is_infinite() && d.is_nan());
        assert_eq!(run("0x1p4", "%lf", vec![&mut d as *mut f64 as u64]), 1);
        assert_eq!(d, 16.0);
        assert_eq!(run("1e", "%lf", vec![&mut d as *mut f64 as u64]), 1);
        assert_eq!(d, 1.0);
        let mut n = 0i32;
        let mut a = 0i32;
        assert_eq!(
            run(
                "42abc",
                "%d%n",
                vec![&mut a as *mut i32 as u64, &mut n as *mut i32 as u64]
            ),
            1
        );
        assert_eq!((a, n), (42, 2));
        assert_eq!(run("x", "%d", vec![&mut a as *mut i32 as u64]), 0);
        assert_eq!(
            run("", "%d", vec![&mut a as *mut i32 as u64]),
            super::super::EOF
        );
        assert_eq!(
            run("   ", "%d", vec![&mut a as *mut i32 as u64]),
            super::super::EOF
        );
        assert_eq!(
            run(
                "5",
                "%d %d",
                vec![&mut a as *mut i32 as u64, &mut n as *mut i32 as u64]
            ),
            1
        );
        assert_eq!(run("7 %", "%d %%", vec![&mut a as *mut i32 as u64]), 1);
        assert_eq!(
            run(
                "1,2",
                "%d,%d",
                vec![&mut a as *mut i32 as u64, &mut n as *mut i32 as u64]
            ),
            2
        );
        assert_eq!((a, n), (1, 2));
        assert_eq!(
            run(
                "1;2",
                "%d,%d",
                vec![&mut a as *mut i32 as u64, &mut n as *mut i32 as u64]
            ),
            1
        );
        assert_eq!(run("9 8", "%*d %d", vec![&mut a as *mut i32 as u64]), 1);
        assert_eq!(a, 8);
        let mut w = [0u32; 4];
        assert_eq!(run("héllo", "%2ls", vec![w.as_mut_ptr() as u64]), 1);
        assert_eq!(w, [b'h' as u32, 0xe9, 0, 0]);
        let mut p = 0u64;
        assert_eq!(run("0x1234", "%p", vec![&mut p as *mut u64 as u64]), 1);
        assert_eq!(p, 0x1234);
    }

    #[test]
    fn prefix_checks() {
        assert!(float_accepts(b"", b'-'));
        assert!(float_accepts(b"-", b'.'));
        assert!(!float_accepts(b"-", b'-'));
        assert!(float_accepts(b"1", b'e'));
        assert!(!float_accepts(b".", b'e'));
        assert!(float_accepts(b"1e", b'-'));
        assert!(!float_accepts(b"1e-", b'-'));
        assert!(float_accepts(b"0", b'x'));
        assert!(float_accepts(b"0x1", b'p'));
        assert!(float_accepts(b"0x", b'a'));
        assert!(!float_accepts(b"1", b'p'));
        assert!(float_accepts(b"i", b'n'));
        assert!(float_accepts(b"inf", b'i'));
        assert!(!float_accepts(b"inf", b'x'));
        assert!(!float_accepts(b"nan", b'a'));
        assert!(int_accepts(b"", b'-', 10));
        assert!(!int_accepts(b"-", b'-', 10));
        assert!(int_accepts(b"0", b'x', 16));
        assert!(!int_accepts(b"0", b'x', 10));
        assert!(int_accepts(b"0x", b'f', 0));
        assert!(!int_accepts(b"0", b'9', 0));
        assert!(int_accepts(b"1", b'9', 0));
    }
}
