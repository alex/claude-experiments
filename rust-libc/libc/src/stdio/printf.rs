//! The `printf` family.
//!
//! [`format`] walks the format string and writes to a [`Sink`]. Integer
//! conversions are formatted by hand; floating-point conversions use
//! `core::fmt` for the digit generation (exact, correctly rounded) and
//! then reshape the result into C's syntax. Hexadecimal floats are done
//! by hand.
//!
//! `%n` is not supported: it is the classic vector for turning a format
//! string bug into a write primitive, and it is refused with `EINVAL`.

use super::{File, lock, stderr, stdout};
use crate::arch::va::VaList;
use crate::c_char;
use crate::errno::Errno;
use crate::malloc;
use core::ffi::c_int;
use core::fmt::Write as _;
use core::mem::MaybeUninit;
use core::ptr;

/// Destination of formatted output.
pub trait Sink {
    /// Writes all of `data`; `false` means a write error.
    fn write(&mut self, data: &[u8]) -> bool;
}

/// A sink that stages output for an unbuffered stream (or a raw file
/// descriptor) so that one `printf` call becomes one `write`.
pub struct Staged<'a> {
    file: &'a mut File,
    buf: [u8; 512],
    len: usize,
}

impl<'a> Staged<'a> {
    /// Creates a staging sink on top of `file`.
    pub fn new(file: &'a mut File) -> Self {
        Staged {
            file,
            buf: [0; 512],
            len: 0,
        }
    }

    /// Flushes what is staged.
    pub fn finish(&mut self) -> bool {
        if self.len == 0 {
            return true;
        }
        let ok = self.file.write_bytes(&self.buf[..self.len]).is_ok();
        self.len = 0;
        ok
    }
}

impl Sink for Staged<'_> {
    fn write(&mut self, data: &[u8]) -> bool {
        if data.len() > self.buf.len() - self.len {
            if !self.finish() {
                return false;
            }
            if data.len() > self.buf.len() {
                return self.file.write_bytes(data).is_ok();
            }
        }
        self.buf[self.len..self.len + data.len()].copy_from_slice(data);
        self.len += data.len();
        true
    }
}

impl Sink for File {
    fn write(&mut self, data: &[u8]) -> bool {
        self.write_bytes(data).is_ok()
    }
}

/// `snprintf` destination: stores at most `cap - 1` bytes.
struct Bounded {
    dst: *mut u8,
    cap: usize,
    len: usize,
}

impl Sink for Bounded {
    fn write(&mut self, data: &[u8]) -> bool {
        let room = self.cap.saturating_sub(1).saturating_sub(self.len);
        let n = data.len().min(room);
        if n > 0 {
            // SAFETY: `dst` has `cap` bytes and `len + n < cap`.
            unsafe { ptr::copy_nonoverlapping(data.as_ptr(), self.dst.add(self.len), n) };
        }
        self.len += data.len();
        true
    }
}

/// `asprintf` destination: a growing `malloc` buffer.
struct Growing {
    buf: *mut u8,
    cap: usize,
    len: usize,
}

impl Sink for Growing {
    fn write(&mut self, data: &[u8]) -> bool {
        if self.len + data.len() + 1 > self.cap {
            let cap = (self.len + data.len() + 1).max(self.cap * 2).max(64);
            // SAFETY: `buf` is null or our own block.
            let new = unsafe { malloc::realloc_impl(self.buf, cap) };
            if new.is_null() {
                return false;
            }
            self.buf = new;
            self.cap = cap;
        }
        // SAFETY: room was ensured.
        unsafe { ptr::copy_nonoverlapping(data.as_ptr(), self.buf.add(self.len), data.len()) };
        self.len += data.len();
        true
    }
}

/// Raw file descriptor destination (`dprintf`), staged.
struct Fd {
    fd: c_int,
    buf: [u8; 512],
    len: usize,
}

impl Fd {
    fn finish(&mut self) -> bool {
        let ok = crate::sys::write_all(self.fd, &self.buf[..self.len]).is_ok();
        self.len = 0;
        ok
    }
}

impl Sink for Fd {
    fn write(&mut self, data: &[u8]) -> bool {
        if data.len() > self.buf.len() - self.len {
            if !self.finish() {
                return false;
            }
            if data.len() > self.buf.len() {
                return crate::sys::write_all(self.fd, data).is_ok();
            }
        }
        self.buf[self.len..self.len + data.len()].copy_from_slice(data);
        self.len += data.len();
        true
    }
}

/// Counts bytes and forwards to an inner sink.
struct Counting<'a, S: Sink> {
    inner: &'a mut S,
    count: usize,
    failed: bool,
}

impl<S: Sink> Counting<'_, S> {
    #[inline]
    fn put(&mut self, data: &[u8]) {
        if !self.failed && !self.inner.write(data) {
            self.failed = true;
        }
        self.count += data.len();
    }

    fn pad(&mut self, n: usize, b: u8) {
        const SPACES: [u8; 64] = [b' '; 64];
        const ZEROS: [u8; 64] = [b'0'; 64];
        let src = if b == b'0' { &ZEROS } else { &SPACES };
        let mut n = n;
        while n > 0 {
            let k = n.min(64);
            self.put(&src[..k]);
            n -= k;
        }
    }
}

// ---------------------------------------------------------------------
// Conversion specifications.

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

#[derive(Clone, Copy)]
struct Spec {
    left: bool,
    plus: bool,
    space: bool,
    alt: bool,
    zero: bool,
    width: usize,
    precision: Option<usize>,
    length: Length,
    conv: u8,
}

/// What kind of argument a conversion consumes.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ArgKind {
    Int,
    Double,
    LongDouble,
}

/// Argument source: sequential `va_list` or pre-fetched positional
/// arguments.
enum Args<'a> {
    Seq(&'a mut VaList),
    Pos(&'a [u64]),
}

impl Args<'_> {
    /// # Safety
    /// The corresponding argument must exist and have the right kind.
    unsafe fn int(&mut self, index: Option<usize>) -> u64 {
        match self {
            // SAFETY: caller contract.
            Args::Seq(ap) => unsafe { ap.gp() },
            Args::Pos(vals) => vals[index.unwrap_or(0)],
        }
    }

    /// # Safety
    /// The corresponding argument must exist and have the right kind.
    unsafe fn double(&mut self, index: Option<usize>, long_double: bool) -> f64 {
        match self {
            // SAFETY: caller contract.
            Args::Seq(ap) => unsafe {
                if long_double {
                    ap.long_double()
                } else {
                    ap.fp()
                }
            },
            Args::Pos(vals) => f64::from_bits(vals[index.unwrap_or(0)]),
        }
    }
}

/// Reads a decimal number from the format (used for widths, precisions
/// and `n$`). Returns `None` above `INT_MAX`, which also keeps the
/// `usize::MAX` "from argument" marker unambiguous.
fn parse_num(p: &mut *const u8) -> Option<usize> {
    let mut n = 0usize;
    // SAFETY: the format is NUL-terminated; digits never include NUL.
    unsafe {
        while (**p).is_ascii_digit() {
            n = n.checked_mul(10)?.checked_add((**p - b'0') as usize)?;
            if n > c_int::MAX as usize {
                return None;
            }
            *p = p.add(1);
        }
    }
    Some(n)
}

/// Parses one conversion specification after the `%`. On success `p`
/// points past the conversion character. `positions` receives the
/// argument positions (`n$`) of width, precision and value, if given.
///
/// # Safety
/// `p` must point into a NUL-terminated format string.
unsafe fn parse_spec(p: &mut *const u8, positions: &mut [Option<usize>; 3]) -> Option<Spec> {
    let mut spec = Spec {
        left: false,
        plus: false,
        space: false,
        alt: false,
        zero: false,
        width: 0,
        precision: None,
        length: Length::None,
        conv: 0,
    };
    // SAFETY: caller contract; every read stops at NUL.
    unsafe {
        // `n$` for the argument itself.
        if (**p).is_ascii_digit() {
            let save = *p;
            let n = parse_num(p)?;
            if **p == b'$' && n > 0 {
                positions[2] = Some(n);
                *p = p.add(1);
            } else {
                *p = save;
            }
        }
        loop {
            match **p {
                b'-' => spec.left = true,
                b'+' => spec.plus = true,
                b' ' => spec.space = true,
                b'#' => spec.alt = true,
                b'0' => spec.zero = true,
                b'\'' => {}
                _ => break,
            }
            *p = p.add(1);
        }
        if **p == b'*' {
            *p = p.add(1);
            if (**p).is_ascii_digit() {
                let n = parse_num(p)?;
                if **p != b'$' || n == 0 {
                    return None;
                }
                *p = p.add(1);
                positions[0] = Some(n);
            }
            spec.width = usize::MAX; // marker: from argument
        } else {
            spec.width = parse_num(p)?;
        }
        if **p == b'.' {
            *p = p.add(1);
            if **p == b'*' {
                *p = p.add(1);
                if (**p).is_ascii_digit() {
                    let n = parse_num(p)?;
                    if **p != b'$' || n == 0 {
                        return None;
                    }
                    *p = p.add(1);
                    positions[1] = Some(n);
                }
                spec.precision = Some(usize::MAX); // marker: from argument
            } else {
                spec.precision = Some(parse_num(p)?);
            }
        }
        spec.length = match **p {
            b'h' => {
                *p = p.add(1);
                if **p == b'h' {
                    *p = p.add(1);
                    Length::Hh
                } else {
                    Length::H
                }
            }
            b'l' => {
                *p = p.add(1);
                if **p == b'l' {
                    *p = p.add(1);
                    Length::Ll
                } else {
                    Length::L
                }
            }
            b'q' => {
                *p = p.add(1);
                Length::Ll
            }
            b'j' => {
                *p = p.add(1);
                Length::J
            }
            b'z' | b'Z' => {
                *p = p.add(1);
                Length::Z
            }
            b't' => {
                *p = p.add(1);
                Length::T
            }
            b'L' => {
                *p = p.add(1);
                Length::BigL
            }
            _ => Length::None,
        };
        spec.conv = **p;
        if spec.conv == 0 {
            return None;
        }
        *p = p.add(1);
    }
    Some(spec)
}

/// Argument kind consumed by a conversion, or `None` if it takes none.
fn arg_kind(spec: &Spec) -> Option<ArgKind> {
    match spec.conv {
        b'd' | b'i' | b'o' | b'u' | b'x' | b'X' | b'c' | b's' | b'p' | b'C' | b'S' => {
            Some(ArgKind::Int)
        }
        b'f' | b'F' | b'e' | b'E' | b'g' | b'G' | b'a' | b'A' => {
            Some(if spec.length == Length::BigL {
                ArgKind::LongDouble
            } else {
                ArgKind::Double
            })
        }
        _ => None,
    }
}

/// Maximum number of positional arguments.
const MAX_POS: usize = 64;

/// Pre-scans a format using `n$` and fetches every argument in order.
///
/// # Safety
/// `fmt` must be NUL-terminated and the arguments must match.
unsafe fn fetch_positional(
    fmt: *const u8,
    ap: &mut VaList,
    vals: &mut [u64; MAX_POS],
) -> Option<usize> {
    let mut kinds = [None::<ArgKind>; MAX_POS];
    let mut max = 0usize;
    let mut p = fmt;
    // SAFETY: caller contract.
    unsafe {
        while *p != 0 {
            if *p != b'%' {
                p = p.add(1);
                continue;
            }
            p = p.add(1);
            if *p == b'%' {
                p = p.add(1);
                continue;
            }
            let mut positions = [None; 3];
            let spec = parse_spec(&mut p, &mut positions)?;
            let value_kind = arg_kind(&spec);
            for (i, pos) in positions.iter().enumerate() {
                let kind = if i == 2 {
                    value_kind
                } else {
                    Some(ArgKind::Int)
                };
                if let (Some(n), Some(kind)) = (pos, kind) {
                    if *n > MAX_POS {
                        return None;
                    }
                    if kinds[n - 1].is_some_and(|k| k != kind) {
                        return None;
                    }
                    kinds[n - 1] = Some(kind);
                    max = max.max(*n);
                }
            }
        }
        for i in 0..max {
            vals[i] = match kinds[i]? {
                ArgKind::Int => ap.gp(),
                ArgKind::Double => ap.fp().to_bits(),
                ArgKind::LongDouble => ap.long_double().to_bits(),
            };
        }
    }
    Some(max)
}

/// Formats `fmt` with `ap` into `sink`. Returns the number of bytes
/// produced, or -1 (with `errno`) on error.
///
/// # Safety
/// `fmt` must be NUL-terminated and the arguments must match it.
pub unsafe fn format<S: Sink>(sink: &mut S, fmt: *const u8, ap: &mut VaList) -> c_int {
    let mut out = Counting {
        inner: sink,
        count: 0,
        failed: false,
    };
    // Positional arguments (`%2$d`) need all arguments fetched up front.
    // A '$' anywhere is the cheap hint to pre-scan the conversions; only
    // an actual `n$` makes the format positional (a literal "$5" must
    // not).
    let mut vals: [u64; MAX_POS];
    // SAFETY: forwarded.
    let has_dollar = unsafe { !crate::string::search::strchr_ptr(fmt, b'$').is_null() };
    let table: Option<&[u64]> = if has_dollar {
        vals = [0; MAX_POS];
        // SAFETY: forwarded.
        match unsafe { fetch_positional(fmt, ap, &mut vals) } {
            Some(0) => None,
            Some(n) => Some(&vals[..n]),
            None => {
                Errno::EINVAL.set();
                return -1;
            }
        }
    } else {
        None
    };
    let uses_positional = table.is_some();
    let mut args = match table {
        Some(t) => Args::Pos(t),
        None => Args::Seq(ap),
    };
    let mut p = fmt;
    // SAFETY: the format is NUL-terminated; all reads stop at NUL.
    unsafe {
        loop {
            // Copy the literal run up to the next '%'.
            let start = p;
            while *p != 0 && *p != b'%' {
                p = p.add(1);
            }
            if p != start {
                out.put(core::slice::from_raw_parts(
                    start,
                    p as usize - start as usize,
                ));
            }
            if *p == 0 {
                break;
            }
            p = p.add(1);
            if *p == b'%' {
                out.put(b"%");
                p = p.add(1);
                continue;
            }
            let mut positions = [None; 3];
            let Some(mut spec) = parse_spec(&mut p, &mut positions) else {
                Errno::EINVAL.set();
                return -1;
            };
            // Positional and sequential arguments must not be mixed
            // (including `*` widths without a position).
            if (uses_positional != positions[2].is_some() && arg_kind(&spec).is_some())
                || (uses_positional
                    && ((spec.width == usize::MAX && positions[0].is_none())
                        || (spec.precision == Some(usize::MAX) && positions[1].is_none())))
            {
                Errno::EINVAL.set();
                return -1;
            }
            let pos = |n: Option<usize>| n.map(|n| n - 1);
            if spec.width == usize::MAX {
                let w = args.int(pos(positions[0])) as c_int;
                if w < 0 {
                    spec.left = true;
                    spec.width = w.unsigned_abs() as usize;
                } else {
                    spec.width = w as usize;
                }
            }
            if spec.precision == Some(usize::MAX) {
                let pr = args.int(pos(positions[1])) as c_int;
                spec.precision = if pr < 0 { None } else { Some(pr as usize) };
            }
            let index = pos(positions[2]);
            let ok = match spec.conv {
                b'd' | b'i' => {
                    let v = args.int(index);
                    let v = match spec.length {
                        Length::Hh => v as i8 as i64,
                        Length::H => v as i16 as i64,
                        Length::None => v as i32 as i64,
                        _ => v as i64,
                    };
                    fmt_int(&mut out, &spec, v.unsigned_abs(), v < 0);
                    true
                }
                b'o' | b'u' | b'x' | b'X' => {
                    let v = args.int(index);
                    let v = match spec.length {
                        Length::Hh => v as u8 as u64,
                        Length::H => v as u16 as u64,
                        Length::None => v as u32 as u64,
                        _ => v,
                    };
                    fmt_int(&mut out, &spec, v, false);
                    true
                }
                b'c' | b'C' => {
                    let v = args.int(index);
                    if spec.length == Length::L || spec.conv == b'C' {
                        let mut buf = [0u8; 4];
                        let s = encode_utf8(v as u32, &mut buf);
                        fmt_padded(&mut out, &spec, s);
                    } else {
                        fmt_padded(&mut out, &spec, &[v as u8]);
                    }
                    true
                }
                b's' | b'S' => {
                    let s = args.int(index) as usize as *const u8;
                    if spec.length == Length::L || spec.conv == b'S' {
                        fmt_wide_string(&mut out, &spec, s as *const u32);
                    } else if s.is_null() {
                        fmt_padded(&mut out, &spec, b"(null)");
                    } else {
                        let len = match spec.precision {
                            Some(n) => crate::string::search::strnlen(s, n),
                            None => crate::string::search::strlen(s),
                        };
                        fmt_padded(&mut out, &spec, core::slice::from_raw_parts(s, len));
                    }
                    true
                }
                b'p' => {
                    let v = args.int(index);
                    if v == 0 {
                        fmt_padded(&mut out, &spec, b"(nil)");
                    } else {
                        let mut s = spec;
                        s.alt = true;
                        s.conv = b'x';
                        fmt_int(&mut out, &s, v, false);
                    }
                    true
                }
                b'f' | b'F' | b'e' | b'E' | b'g' | b'G' | b'a' | b'A' => {
                    let v = args.double(index, spec.length == Length::BigL);
                    fmt_float(&mut out, &spec, v)
                }
                b'm' => {
                    let msg = crate::string::str::strerror(Errno::get().0);
                    let len = crate::string::search::strlen(msg as *const u8);
                    fmt_padded(
                        &mut out,
                        &spec,
                        core::slice::from_raw_parts(msg as *const u8, len),
                    );
                    true
                }
                _ => false,
            };
            if !ok {
                Errno::EINVAL.set();
                return -1;
            }
        }
    }
    if out.failed {
        return -1;
    }
    match c_int::try_from(out.count) {
        Ok(n) => n,
        Err(_) => {
            Errno::EOVERFLOW.set();
            -1
        }
    }
}

/// Writes `body` padded to the field width.
fn fmt_padded<S: Sink>(out: &mut Counting<'_, S>, spec: &Spec, body: &[u8]) {
    let pad = spec.width.saturating_sub(body.len());
    if !spec.left {
        out.pad(pad, b' ');
    }
    out.put(body);
    if spec.left {
        out.pad(pad, b' ');
    }
}

/// Writes `prefix` + zero padding + `digits`, padded to the field width
/// according to the flags.
fn fmt_number<S: Sink>(
    out: &mut Counting<'_, S>,
    spec: &Spec,
    prefix: &[u8],
    zeros: usize,
    digits: &[u8],
) {
    let body = prefix.len() + zeros + digits.len();
    let pad = spec.width.saturating_sub(body);
    if !spec.left && !spec.zero {
        out.pad(pad, b' ');
    }
    out.put(prefix);
    if !spec.left && spec.zero {
        out.pad(pad, b'0');
    }
    out.pad(zeros, b'0');
    out.put(digits);
    if spec.left {
        out.pad(pad, b' ');
    }
}

/// Formats an integer conversion.
fn fmt_int<S: Sink>(out: &mut Counting<'_, S>, spec: &Spec, magnitude: u64, negative: bool) {
    let mut buf = [0u8; 24];
    let mut i = buf.len();
    let (base, upper) = match spec.conv {
        b'o' => (8, false),
        b'x' => (16, false),
        b'X' => (16, true),
        _ => (10, false),
    };
    let mut v = magnitude;
    // One loop per base, so the divisions are by constants.
    match base {
        10 => {
            while v != 0 {
                i -= 1;
                buf[i] = b'0' + (v % 10) as u8;
                v /= 10;
            }
        }
        16 => {
            let alphabet: &[u8; 16] = if upper {
                b"0123456789ABCDEF"
            } else {
                b"0123456789abcdef"
            };
            while v != 0 {
                i -= 1;
                buf[i] = alphabet[(v & 15) as usize];
                v >>= 4;
            }
        }
        _ => {
            while v != 0 {
                i -= 1;
                buf[i] = b'0' + (v & 7) as u8;
                v >>= 3;
            }
        }
    }
    let mut digits = &buf[i..];
    // Precision: minimum digits; a zero value with precision 0 prints
    // nothing (except that "%#o" still prints "0").
    let mut zeros = 0;
    match spec.precision {
        Some(0) if magnitude == 0 => {
            if spec.alt && base == 8 {
                digits = b"0";
            }
        }
        Some(pr) => zeros = pr.saturating_sub(digits.len()),
        None => {
            if magnitude == 0 {
                digits = b"0";
            }
        }
    }
    if spec.alt && base == 8 && zeros == 0 && digits.first() != Some(&b'0') {
        zeros = 1;
    }
    let prefix: &[u8] = if matches!(spec.conv, b'd' | b'i') {
        if negative {
            b"-"
        } else if spec.plus {
            b"+"
        } else if spec.space {
            b" "
        } else {
            b""
        }
    } else if spec.alt && base == 16 && magnitude != 0 {
        if upper { b"0X" } else { b"0x" }
    } else {
        b""
    };
    // The zero flag is ignored when a precision is given.
    let mut spec = *spec;
    if spec.precision.is_some() {
        spec.zero = false;
    }
    fmt_number(out, &spec, prefix, zeros, digits);
}

/// Encodes a code point as UTF-8 (invalid values become U+FFFD).
fn encode_utf8(cp: u32, buf: &mut [u8; 4]) -> &[u8] {
    let c = char::from_u32(cp).unwrap_or('\u{fffd}');
    c.encode_utf8(buf).as_bytes()
}

/// Formats a `wchar_t` string as UTF-8, honouring the precision as a
/// byte limit that never splits a character.
///
/// # Safety
/// `s` must be null or NUL-terminated.
unsafe fn fmt_wide_string<S: Sink>(out: &mut Counting<'_, S>, spec: &Spec, s: *const u32) {
    if s.is_null() {
        fmt_padded(out, spec, b"(null)");
        return;
    }
    // First pass: measure.
    let limit = spec.precision.unwrap_or(usize::MAX);
    let mut total = 0;
    let mut n = 0;
    let mut buf = [0u8; 4];
    // SAFETY: caller contract.
    unsafe {
        while *s.add(n) != 0 {
            let len = encode_utf8(*s.add(n), &mut buf).len();
            if total + len > limit {
                break;
            }
            total += len;
            n += 1;
        }
    }
    let pad = spec.width.saturating_sub(total);
    if !spec.left {
        out.pad(pad, b' ');
    }
    for i in 0..n {
        // SAFETY: `i < n` was validated above.
        let cp = unsafe { *s.add(i) };
        out.put(encode_utf8(cp, &mut buf));
    }
    if spec.left {
        out.pad(pad, b' ');
    }
}

/// A `core::fmt::Write` over a fixed buffer that fails when full. The
/// buffer is uninitialised storage so that the (large) float buffers do
/// not have to be zeroed on every call; only `[..len]` is ever read.
struct Fixed<'a> {
    buf: &'a mut [MaybeUninit<u8>],
    len: usize,
}

impl<'a> Fixed<'a> {
    fn new(buf: &'a mut [MaybeUninit<u8>]) -> Self {
        Fixed { buf, len: 0 }
    }

    /// The bytes written so far.
    fn as_bytes(&self) -> &[u8] {
        // SAFETY: `[..len]` has been written by `write_str`/`insert`.
        unsafe { core::slice::from_raw_parts(self.buf.as_ptr() as *const u8, self.len) }
    }

    /// Appends one byte.
    #[inline]
    fn push(&mut self, b: u8) -> bool {
        if self.len == self.buf.len() {
            return false;
        }
        self.buf[self.len] = MaybeUninit::new(b);
        self.len += 1;
        true
    }

    /// Appends the exponent suffix `e±dd` (at least two digits).
    fn push_exponent(&mut self, e: u8, exp: i32) -> bool {
        let mag = exp.unsigned_abs();
        let mut digits = [0u8; 10];
        let mut n = 0;
        let mut v = mag;
        while v > 0 || n < 2 {
            digits[n] = b'0' + (v % 10) as u8;
            v /= 10;
            n += 1;
        }
        if !self.push(e) || !self.push(if exp < 0 { b'-' } else { b'+' }) {
            return false;
        }
        while n > 0 {
            n -= 1;
            if !self.push(digits[n]) {
                return false;
            }
        }
        true
    }

    /// Removes `[from, to)`.
    fn remove(&mut self, from: usize, to: usize) {
        self.buf.copy_within(to..self.len, from);
        self.len -= to - from;
    }
}

impl core::fmt::Write for Fixed<'_> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        if s.len() > self.buf.len() - self.len {
            return Err(core::fmt::Error);
        }
        // SAFETY: the destination is inside the buffer and does not
        // overlap the source.
        unsafe {
            core::ptr::copy_nonoverlapping(
                s.as_ptr(),
                self.buf.as_mut_ptr().add(self.len) as *mut u8,
                s.len(),
            );
        }
        self.len += s.len();
        Ok(())
    }
}

/// No double has more than 1074 fractional digits or 767 significant
/// digits, so precisions beyond these produce only zeros, which are
/// appended without going through `core::fmt`.
const MAX_FRAC_DIGITS: usize = 1074;
const MAX_SIG_DIGITS: usize = 800;
/// Room for the longest `%f`: 309 integer digits, the point, 1074
/// fractional digits.
const FLOAT_BUF: usize = 1400;

/// Significant digits of a finite non-negative double, and the decimal
/// exponent of the first one. Digits past `len` read as zero.
struct Short {
    buf: [u8; 20],
    len: usize,
    exp: i32,
}

impl Short {
    /// Parses `core::fmt`'s `{:e}` output (`d.ddde±x`) into `buf`.
    fn parse(s: &[u8], buf: &mut [u8]) -> (usize, i32) {
        let epos = s.iter().position(|&b| b == b'e').unwrap_or(s.len());
        let mut len = 0;
        for &b in &s[..epos] {
            if b != b'.' && len < buf.len() {
                buf[len] = b;
                len += 1;
            }
        }
        (len, parse_i32(s.get(epos + 1..).unwrap_or(b"0")))
    }

    /// Rounds to `n` significant digits the way the true binary value
    /// rounds (which is what C requires). Returns false when that cannot
    /// be decided from the shortest digits alone (see [`with_digits`]);
    /// the digits are then unchanged.
    fn round(&mut self, n: usize) -> bool {
        if n >= self.len {
            // Padding with zeros is exact only while a unit of the last
            // requested digit exceeds the half-ulp uncertainty.
            return n <= 15;
        }
        let dropped = &self.buf[n..self.len];
        // Position relative to the halfway point "500...".
        let up = match dropped[0].cmp(&b'5') {
            core::cmp::Ordering::Greater => true,
            core::cmp::Ordering::Less => false,
            core::cmp::Ordering::Equal => {
                if dropped[1..].iter().all(|&b| b == b'0') {
                    // An exact tie in the shortest digits says nothing
                    // about which side the true value is on.
                    return false;
                }
                true
            }
        };
        if self.len >= 16 {
            // With 16 or 17 digits a unit of the last digit is below the
            // half-ulp uncertainty of the shortest form; require a safe
            // margin from the halfway point.
            let m = dropped.len();
            let value = dropped
                .iter()
                .fold(0u64, |a, &d| a * 10 + (d - b'0') as u64);
            let tie = 5 * 10u64.pow(m as u32 - 1);
            if value.abs_diff(tie) < 25 {
                return false;
            }
        }
        self.len = n;
        if up {
            // Increment with carry; a carry out of the first digit makes
            // the number a power of ten with one more exponent.
            let mut i = n;
            loop {
                if i == 0 {
                    self.buf[0] = b'1';
                    self.len = 1;
                    self.exp += 1;
                    break;
                }
                i -= 1;
                if self.buf[i] == b'9' {
                    self.buf[i] = b'0';
                } else {
                    self.buf[i] += 1;
                    break;
                }
            }
        }
        if self.len == 0 {
            // Rounded to zero.
            self.exp = -1;
        }
        true
    }
}

/// The digits of the shortest decimal that reads back as `x`, from
/// `core::fmt`'s Grisu/Dragon shortest mode (much faster than its exact
/// fixed-precision mode).
fn short_digits(x: f64) -> Short {
    let mut storage = [MaybeUninit::<u8>::uninit(); 32];
    let mut tmp = Fixed::new(&mut storage);
    // Cannot fail: the shortest form is at most 24 bytes.
    let _ = write!(tmp, "{x:e}");
    let mut d = Short {
        buf: [b'0'; 20],
        len: 0,
        exp: 0,
    };
    (d.len, d.exp) = Short::parse(tmp.as_bytes(), &mut d.buf);
    d
}

/// The digits of `x` correctly rounded to `n >= 1` significant digits
/// (beyond [`MAX_SIG_DIGITS`] they are zeros, since no double has more),
/// from `core::fmt`'s exact mode.
fn exact_digits(x: f64, n: usize, out: &mut [u8; MAX_SIG_DIGITS + 1]) -> Option<(usize, i32)> {
    let mut storage = [MaybeUninit::<u8>::uninit(); FLOAT_BUF];
    let mut tmp = Fixed::new(&mut storage);
    let p = n.min(MAX_SIG_DIGITS + 1) - 1;
    write!(tmp, "{x:.p$e}").ok()?;
    Some(Short::parse(tmp.as_bytes(), out))
}

/// Calls `f` with the digits of `x` correctly rounded to `n` significant
/// digits (`n <= 0` means the value rounds to zero or to a power of ten)
/// and their exponent. Returns `None` if the shortest digits cannot
/// decide the rounding, in which case the caller must use the exact mode.
///
/// Rounding the shortest representation `S` is exact when no rounding
/// boundary lies within half an ulp (`2^-53 |x|`) of `S`, because the
/// true value is that close to `S`. With at most 15 digits a unit of the
/// last digit already exceeds that distance, so only an exact tie is
/// undecidable; with 16 or 17 digits [`Short::round`] additionally
/// requires a margin of 25 units.
fn with_digits(mut d: Short, n: i64, f: impl FnOnce(&[u8], i32) -> bool) -> Option<bool> {
    if n < 0 {
        // Even rounding up could not reach the first kept digit.
        return Some(f(b"", -1));
    }
    if !d.round(n as usize) {
        return None;
    }
    Some(f(&d.buf[..d.len], d.exp))
}

/// Writes `digits` (exponent `exp`) in fixed notation with `frac`
/// fraction digits.
fn build_fixed(buf: &mut Fixed<'_>, digits: &[u8], exp: i32, frac: usize, alt: bool) -> bool {
    let at = |i: usize| digits.get(i).copied().unwrap_or(b'0');
    let mut push = |b: u8| buf.push(b);
    if exp >= 0 {
        let n_int = exp as usize + 1;
        for i in 0..n_int {
            if !push(at(i)) {
                return false;
            }
        }
        if (frac > 0 || alt) && !push(b'.') {
            return false;
        }
        for i in 0..frac {
            if !push(at(n_int + i)) {
                return false;
            }
        }
    } else {
        if !push(b'0') || ((frac > 0 || alt) && !push(b'.')) {
            return false;
        }
        let lead = (-exp - 1) as usize;
        for i in 0..frac {
            let b = if i < lead { b'0' } else { at(i - lead) };
            if !push(b) {
                return false;
            }
        }
    }
    true
}

/// Writes `digits` (exponent `exp`) in C's `%e` notation with `frac`
/// fraction digits.
fn build_exp(
    buf: &mut Fixed<'_>,
    digits: &[u8],
    exp: i32,
    frac: usize,
    upper: bool,
    alt: bool,
) -> bool {
    let at = |i: usize| digits.get(i).copied().unwrap_or(b'0');
    if !buf.push(at(0)) || ((frac > 0 || alt) && !buf.push(b'.')) {
        return false;
    }
    for i in 0..frac {
        if !buf.push(at(1 + i)) {
            return false;
        }
    }
    buf.push_exponent(if upper { b'E' } else { b'e' }, exp)
}

/// Formats a floating-point conversion. Returns false on an internal
/// error (which cannot happen for well-formed specs).
fn fmt_float<S: Sink>(out: &mut Counting<'_, S>, spec: &Spec, x: f64) -> bool {
    let upper = spec.conv.is_ascii_uppercase();
    let negative = x.is_sign_negative();
    let prefix: &[u8] = if negative {
        b"-"
    } else if spec.plus {
        b"+"
    } else if spec.space {
        b" "
    } else {
        b""
    };
    if !x.is_finite() {
        let body: &[u8] = match (x.is_nan(), upper) {
            (true, false) => b"nan",
            (true, true) => b"NAN",
            (false, false) => b"inf",
            (false, true) => b"INF",
        };
        let mut s = *spec;
        s.zero = false;
        fmt_number(out, &s, prefix, 0, body);
        return true;
    }
    let x = x.abs();
    let mut storage = [MaybeUninit::<u8>::uninit(); FLOAT_BUF];
    let mut buf = Fixed::new(&mut storage);
    let mut extra_zeros = 0;
    // The shortest digits decide roundings to at most 15 significant
    // digits; for longer requests go straight to the exact mode.
    let ok = match spec.conv {
        b'f' | b'F' => {
            let p = spec.precision.unwrap_or(6);
            let quick = if p <= 15 {
                let short = short_digits(x);
                // Significant digits kept depend on the magnitude.
                let n = short.exp as i64 + 1 + p as i64;
                with_digits(short, n, |d, e| build_fixed(&mut buf, d, e, p, spec.alt))
            } else {
                None
            };
            match quick {
                Some(ok) => ok,
                None => {
                    let p1 = p.min(MAX_FRAC_DIGITS);
                    extra_zeros = p - p1;
                    let ok = write!(buf, "{x:.p1$}").is_ok();
                    if ok && spec.alt && p == 0 {
                        let _ = buf.write_str(".");
                    }
                    ok
                }
            }
        }
        b'e' | b'E' => {
            let p = spec.precision.unwrap_or(6);
            let quick = if p < 15 {
                with_digits(short_digits(x), p as i64 + 1, |d, e| {
                    build_exp(&mut buf, d, e, p, upper, spec.alt)
                })
            } else {
                None
            };
            match quick {
                Some(ok) => ok,
                None => {
                    // Digits past the exact expansion are zeros and are
                    // emitted by `finish_float` rather than buffered.
                    let p1 = p.min(MAX_SIG_DIGITS);
                    extra_zeros = p - p1;
                    let mut big = [0u8; MAX_SIG_DIGITS + 1];
                    match exact_digits(x, p1 + 1, &mut big) {
                        Some((len, e)) => build_exp(&mut buf, &big[..len], e, p1, upper, spec.alt),
                        None => false,
                    }
                }
            }
        }
        b'g' | b'G' => {
            let p = spec.precision.unwrap_or(6).max(1);
            // Style depends on the exponent after rounding to `p` digits.
            // Returns the number of trailing zeros left for `finish_float`
            // to emit when the precision exceeds the buffer.
            let general = |buf: &mut Fixed<'_>, d: &[u8], e: i32| -> Option<usize> {
                let exp = if x == 0.0 { 0 } else { e };
                if exp >= -4 && (exp as i64) < p as i64 {
                    let frac = (p as i64 - 1 - exp as i64) as usize;
                    let f1 = frac.min(MAX_FRAC_DIGITS);
                    build_fixed(buf, d, e, f1, spec.alt).then_some(frac - f1)
                } else {
                    let f1 = (p - 1).min(MAX_SIG_DIGITS);
                    build_exp(buf, d, e, f1, upper, spec.alt).then_some(p - 1 - f1)
                }
            };
            let mut zeros = 0;
            let mut run = |buf: &mut Fixed<'_>, d: &[u8], e: i32| match general(buf, d, e) {
                Some(z) => {
                    zeros = z;
                    true
                }
                None => false,
            };
            let quick = if p <= 15 {
                with_digits(short_digits(x), p as i64, |d, e| run(&mut buf, d, e))
            } else {
                None
            };
            let ok = match quick {
                Some(ok) => ok,
                None => {
                    let mut big = [0u8; MAX_SIG_DIGITS + 1];
                    match exact_digits(x, p, &mut big) {
                        Some((len, e)) => run(&mut buf, &big[..len], e),
                        None => false,
                    }
                }
            };
            if ok && !spec.alt {
                // The unbuffered digits are all zeros, so dropping them
                // and stripping the buffer is the same as stripping all.
                strip_trailing_zeros(&mut buf);
            } else {
                extra_zeros = zeros;
            }
            ok
        }
        b'a' | b'A' => {
            // 13 hex digits show the whole mantissa; the rest are zeros.
            let precision = spec.precision.map(|p| {
                let p1 = p.min(13);
                extra_zeros = p - p1;
                p1
            });
            fmt_hex_float(&mut buf, x, precision, upper, spec.alt)
        }
        _ => false,
    };
    ok && finish_float(out, spec, prefix, &buf, extra_zeros)
}

/// Pads and emits a formatted float body.
fn finish_float<S: Sink>(
    out: &mut Counting<'_, S>,
    spec: &Spec,
    prefix: &[u8],
    buf: &Fixed<'_>,
    extra_zeros: usize,
) -> bool {
    let body = buf.as_bytes();
    // For hex floats the "0x" belongs before any zero padding.
    let (radix, body) = if matches!(spec.conv, b'a' | b'A') {
        body.split_at(2)
    } else {
        (&b""[..], body)
    };
    // `extra_zeros` belong at the end of the fraction, i.e. before any
    // exponent.
    let split = if extra_zeros > 0 {
        body.iter()
            .position(|&b| matches!(b, b'e' | b'E' | b'p' | b'P'))
            .unwrap_or(body.len())
    } else {
        body.len()
    };
    let width_body = radix.len() + body.len() + extra_zeros;
    let pad = spec.width.saturating_sub(prefix.len() + width_body);
    if !spec.left && !spec.zero {
        out.pad(pad, b' ');
    }
    out.put(prefix);
    out.put(radix);
    if !spec.left && spec.zero {
        out.pad(pad, b'0');
    }
    out.put(&body[..split]);
    out.pad(extra_zeros, b'0');
    out.put(&body[split..]);
    if spec.left {
        out.pad(pad, b' ');
    }
    true
}

fn parse_i32(s: &[u8]) -> i32 {
    let (neg, digits) = match s.first() {
        Some(b'-') => (true, &s[1..]),
        _ => (false, s),
    };
    let v = digits.iter().fold(0i32, |a, &d| a * 10 + (d - b'0') as i32);
    if neg { -v } else { v }
}

/// Removes trailing zeros (and a bare point) from the fraction part of a
/// `%g` result, keeping any exponent suffix.
fn strip_trailing_zeros(buf: &mut Fixed<'_>) {
    let s = buf.as_bytes();
    let Some(point) = s.iter().position(|&b| b == b'.') else {
        return;
    };
    let epos = s
        .iter()
        .position(|&b| b == b'e' || b == b'E')
        .unwrap_or(s.len());
    let mut end = epos;
    while end > point + 1 && s[end - 1] == b'0' {
        end -= 1;
    }
    if end == point + 1 {
        end = point;
    }
    if end != epos {
        buf.remove(end, epos);
    }
}

/// Writes `x` in C's `%a` form.
fn fmt_hex_float(
    buf: &mut Fixed<'_>,
    x: f64,
    precision: Option<usize>,
    upper: bool,
    alt: bool,
) -> bool {
    let bits = x.to_bits();
    let exp_bits = ((bits >> 52) & 0x7ff) as i32;
    let mut frac = bits & ((1u64 << 52) - 1);
    let (mut lead, exp) = if exp_bits == 0 {
        if frac == 0 {
            (0u64, 0i32)
        } else {
            // Subnormal: normalise so the leading digit is 1.
            let shift = frac.leading_zeros() as i32 - 11;
            frac <<= shift;
            frac &= (1u64 << 52) - 1;
            (1, -1022 - shift)
        }
    } else {
        (1, exp_bits - 1023)
    };
    // Round the 13 hex fraction digits to the precision.
    let mut ndigits = 13usize;
    if let Some(p) = precision {
        if p < 13 {
            let drop = 4 * (13 - p) as u32;
            let rem = frac & ((1u64 << drop) - 1);
            let half = 1u64 << (drop - 1);
            // Round half to even over the kept bits, leading digit included.
            let mut kept = (lead << (52 - drop)) | (frac >> drop);
            if rem > half || (rem == half && kept & 1 == 1) {
                kept += 1;
            }
            lead = kept >> (52 - drop);
            frac = (kept & ((1u64 << (52 - drop)) - 1)) << drop;
            ndigits = p;
        }
    } else {
        while ndigits > 0 && frac & 0xf == 0 {
            frac >>= 4;
            ndigits -= 1;
        }
        frac <<= 4 * (13 - ndigits);
    }
    if buf.write_str(if upper { "0X" } else { "0x" }).is_err() {
        return false;
    }
    if write!(buf, "{lead}").is_err() {
        return false;
    }
    let total = precision.unwrap_or(ndigits);
    if total > 0 || alt {
        if buf.write_str(".").is_err() {
            return false;
        }
        for i in 0..total {
            let d = if i < 13 {
                ((frac >> (48 - 4 * i)) & 0xf) as u8
            } else {
                0
            };
            let c = if d < 10 {
                b'0' + d
            } else if upper {
                b'A' + d - 10
            } else {
                b'a' + d - 10
            };
            if !buf.push(c) {
                return false;
            }
        }
    }
    // `%a` exponents have no minimum digit count.
    let mag = exp.unsigned_abs();
    let mut storage = [MaybeUninit::<u8>::uninit(); 16];
    let mut tmp = Fixed::new(&mut storage);
    let _ = write!(tmp, "{mag}");
    if !buf.push(if upper { b'P' } else { b'p' }) || !buf.push(if exp < 0 { b'-' } else { b'+' }) {
        return false;
    }
    let digits = tmp.as_bytes();
    for &d in digits {
        if !buf.push(d) {
            return false;
        }
    }
    true
}

// ---------------------------------------------------------------------
// The C API.

/// `vfprintf(3)`.
///
/// # Safety
/// `f` must be a valid stream; `fmt` NUL-terminated with matching args.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vfprintf(f: *mut File, fmt: *const c_char, ap: *mut VaList) -> c_int {
    // SAFETY: forwarded.
    let mut g = unsafe { lock(f) };
    if g.is_unbuffered() {
        let mut staged = Staged::new(&mut g);
        // SAFETY: forwarded.
        let n = unsafe { format(&mut staged, fmt as *const u8, &mut *ap) };
        if !staged.finish() {
            return -1;
        }
        n
    } else {
        // SAFETY: forwarded.
        unsafe { format(&mut *g, fmt as *const u8, &mut *ap) }
    }
}

/// `vprintf(3)`.
///
/// # Safety
/// `fmt` must be NUL-terminated with matching args.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vprintf(fmt: *const c_char, ap: *mut VaList) -> c_int {
    // SAFETY: forwarded; stdout is always valid.
    unsafe { vfprintf(stdout, fmt, ap) }
}

/// `vsnprintf(3)`.
///
/// # Safety
/// `s` must be valid for `n` bytes; `fmt` NUL-terminated with matching
/// args.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vsnprintf(
    s: *mut c_char,
    n: usize,
    fmt: *const c_char,
    ap: *mut VaList,
) -> c_int {
    let mut sink = Bounded {
        dst: s as *mut u8,
        cap: n,
        len: 0,
    };
    // SAFETY: forwarded.
    let r = unsafe { format(&mut sink, fmt as *const u8, &mut *ap) };
    if n > 0 {
        let end = sink.len.min(n - 1);
        // SAFETY: `end < n`.
        unsafe { *s.add(end) = 0 };
    }
    r
}

/// `vsprintf(3)`.
///
/// # Safety
/// `s` must be large enough for the output.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vsprintf(s: *mut c_char, fmt: *const c_char, ap: *mut VaList) -> c_int {
    // SAFETY: forwarded.
    unsafe { vsnprintf(s, isize::MAX as usize, fmt, ap) }
}

/// `vasprintf(3)`.
///
/// # Safety
/// `out` must be valid; `fmt` NUL-terminated with matching args.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vasprintf(
    out: *mut *mut c_char,
    fmt: *const c_char,
    ap: *mut VaList,
) -> c_int {
    let mut sink = Growing {
        buf: ptr::null_mut(),
        cap: 0,
        len: 0,
    };
    // SAFETY: forwarded.
    let r = unsafe { format(&mut sink, fmt as *const u8, &mut *ap) };
    if r < 0 || !sink.write(b"\0") {
        // SAFETY: our own block (or null).
        unsafe { malloc::dealloc(sink.buf) };
        // SAFETY: caller contract.
        unsafe { *out = ptr::null_mut() };
        return -1;
    }
    // SAFETY: caller contract.
    unsafe { *out = sink.buf as *mut c_char };
    r
}

/// `vdprintf(3)`.
///
/// # Safety
/// `fmt` must be NUL-terminated with matching args.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vdprintf(fd: c_int, fmt: *const c_char, ap: *mut VaList) -> c_int {
    let mut sink = Fd {
        fd,
        buf: [0; 512],
        len: 0,
    };
    // SAFETY: forwarded.
    let r = unsafe { format(&mut sink, fmt as *const u8, &mut *ap) };
    if !sink.finish() {
        return -1;
    }
    r
}

/// Convenience for internal callers: formats to stderr.
///
/// # Safety
/// As for [`vfprintf`].
pub unsafe fn veprintf(fmt: *const c_char, ap: *mut VaList) -> c_int {
    // SAFETY: forwarded; stderr is always valid.
    unsafe { vfprintf(stderr, fmt, ap) }
}

#[cfg(not(test))]
mod stubs {
    use crate::arch::va::variadic_stub;
    variadic_stub!(printf, 1, "rsi", super::vprintf);
    variadic_stub!(fprintf, 2, "rdx", super::vfprintf);
    variadic_stub!(dprintf, 2, "rdx", super::vdprintf);
    variadic_stub!(sprintf, 2, "rdx", super::vsprintf);
    variadic_stub!(snprintf, 3, "rcx", super::vsnprintf);
    variadic_stub!(asprintf, 2, "rdx", super::vasprintf);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Builds a `VaList` over the given 64-bit words as if they had been
    /// passed on the stack (all in the overflow area), which is how a C
    /// caller passes arguments beyond the register slots.
    struct FakeArgs {
        words: Vec<u64>,
    }

    impl FakeArgs {
        fn list(&mut self) -> VaList {
            // SAFETY: VaList is repr(C) with the documented layout; we
            // build it with both register areas exhausted.
            unsafe {
                core::mem::transmute::<[u64; 3], VaList>([
                    (6 * 8) as u64 | ((6 * 8 + 8 * 16) as u64) << 32,
                    self.words.as_mut_ptr() as u64,
                    0,
                ])
            }
        }
    }

    struct VecSink(Vec<u8>);
    impl Sink for VecSink {
        fn write(&mut self, data: &[u8]) -> bool {
            self.0.extend_from_slice(data);
            true
        }
    }

    fn run(fmt: &str, words: Vec<u64>) -> (c_int, String) {
        let cfmt = std::ffi::CString::new(fmt).unwrap();
        let mut args = FakeArgs { words };
        let mut ap = args.list();
        let mut sink = VecSink(Vec::new());
        // SAFETY: the fake arguments match the format.
        let n = unsafe { format(&mut sink, cfmt.as_ptr() as *const u8, &mut ap) };
        (n, String::from_utf8(sink.0).unwrap())
    }

    /// Rough per-call timings, for development: `cargo test -p rustlibc
    /// -- --ignored --nocapture timing`.
    #[test]
    #[ignore]
    fn timing() {
        let cases: [(&str, f64); 7] = [
            ("%f", 3.14159 * 12345.0),
            ("%f", 0.25 * 17.0),
            ("%e", 3.14159 * 12345.0),
            ("%g", 2.5e-7 * 17.0),
            ("%g", 0.25 * 17.0),
            ("%.17g", 0.1 * 17.0),
            ("%d", 12345.0),
        ];
        for (fmt, x) in cases {
            let cfmt = std::ffi::CString::new(fmt).unwrap();
            let word = if fmt == "%d" { x as u64 } else { x.to_bits() };
            let n = 200_000;
            let t = std::time::Instant::now();
            for _ in 0..n {
                let mut args = FakeArgs { words: vec![word] };
                let mut ap = args.list();
                let mut sink = VecSink(Vec::with_capacity(64));
                // SAFETY: the fake arguments match the format.
                let r = unsafe { format(&mut sink, cfmt.as_ptr() as *const u8, &mut ap) };
                std::hint::black_box((r, sink));
            }
            let per = t.elapsed().as_nanos() as f64 / n as f64;
            let t = std::time::Instant::now();
            for _ in 0..n {
                std::hint::black_box(short_digits(std::hint::black_box(x)));
            }
            let short = t.elapsed().as_nanos() as f64 / n as f64;
            println!("{fmt:8} {x:<12} {per:6.0} ns  (short_digits {short:4.0} ns)");
        }
    }

    fn check(fmt: &str, words: Vec<u64>, expected: &str) {
        let (n, s) = run(fmt, words);
        assert_eq!(s, expected, "format {fmt:?}");
        assert_eq!(n as usize, expected.len(), "format {fmt:?}");
    }

    fn f(x: f64) -> u64 {
        x.to_bits()
    }

    fn s(text: &'static str) -> u64 {
        // Leak a C string for the test.
        let c = std::ffi::CString::new(text).unwrap();
        c.into_raw() as u64
    }

    #[test]
    fn integers() {
        check(
            "%d|%i|%u",
            vec![42, (-7i32) as u32 as u64, 3_000_000_000u64],
            "42|-7|3000000000",
        );
        check(
            "%ld %lld %zu %jd %td",
            vec![
                (-5i64) as u64,
                1 << 40,
                usize::MAX as u64,
                9,
                (-3i64) as u64,
            ],
            "-5 1099511627776 18446744073709551615 9 -3",
        );
        check(
            "%hhd %hd %hhu %hu",
            vec![300, 70000, 300, 70000],
            "44 4464 44 4464",
        );
        check(
            "%x %X %o %#x %#X %#o",
            vec![255, 255, 8, 255, 255, 8],
            "ff FF 10 0xff 0XFF 010",
        );
        check("%#x %#o %o", vec![0, 0, 0], "0 0 0");
        check(
            "[%5d] [%-5d] [%05d] [%+d] [% d] [%+d]",
            vec![42, 42, 42, 42, 42, (-42i32) as u32 as u64],
            "[   42] [42   ] [00042] [+42] [ 42] [-42]",
        );
        check(
            "[%.5d] [%.0d] [%.0d] [%5.3d] [%-8.3d] [%08.3d]",
            vec![42, 0, 7, 42, 42, 42],
            "[00042] [] [7] [  042] [042     ] [     042]",
        );
        check("%c%c%%", vec![b'a' as u64, b'z' as u64], "az%");
        check(
            "[%3c] [%-3c]",
            vec![b'a' as u64, b'b' as u64],
            "[  a] [b  ]",
        );
        check("%d", vec![i32::MIN as u32 as u64], "-2147483648");
        check("%lld", vec![i64::MIN as u64], "-9223372036854775808");
        check("%*d|%-*d|%.*d", vec![5, 42, 5, 42, 3, 7], "   42|42   |007");
        check("%*d", vec![(-5i32) as u32 as u64, 42], "42   ");
        check("%.*d", vec![(-1i32) as u32 as u64, 42], "42");
    }

    #[test]
    fn strings_and_pointers() {
        check(
            "%s|%5s|%-5s|%.2s|%.10s",
            vec![s("abc"), s("abc"), s("abc"), s("abc"), s("abc")],
            "abc|  abc|abc  |ab|abc",
        );
        check("%s", vec![0], "(null)");
        check("%p", vec![0x1234], "0x1234");
        check("%p", vec![0], "(nil)");
        check("%10p|%-10p|", vec![0xabc, 0xabc], "     0xabc|0xabc     |");
        check(
            "%ls|%.3ls",
            vec![
                vec![0x68u32, 0xe9, 0x4e16, 0].leak().as_ptr() as u64,
                vec![0x68u32, 0xe9, 0x4e16, 0].leak().as_ptr() as u64,
            ],
            "hé世|hé",
        );
        check("%lc%lc", vec![0x263a, b'x' as u64], "☺x");
    }

    #[test]
    fn floats_fixed_and_exp() {
        check(
            "%f %f %f",
            vec![f(0.0), f(1.5), f(-2.25)],
            "0.000000 1.500000 -2.250000",
        );
        check(
            "%.2f %.0f %#.0f %.10f",
            vec![f(3.14159), f(2.5), f(2.5), f(0.1)],
            "3.14 2 2. 0.1000000000",
        );
        check("%.0f %.0f %.0f", vec![f(0.5), f(1.5), f(3.5)], "0 2 4");
        check(
            "%e %E %.2e %.0e %#.0e",
            vec![f(12345.678), f(0.00012), f(-1.5), f(15.0), f(15.0)],
            "1.234568e+04 1.200000E-04 -1.50e+00 2e+01 2.e+01",
        );
        check(
            "%e %e",
            vec![f(1e300), f(1e-300)],
            "1.000000e+300 1.000000e-300",
        );
        check("%f", vec![f(1e20)], "100000000000000000000.000000");
        check("%.3f", vec![f(1e-10)], "0.000");
        check(
            "[%10.3f] [%-10.3f] [%010.3f] [%+.1f] [% .1f]",
            vec![f(3.14159); 5],
            "[     3.142] [3.142     ] [000003.142] [+3.1] [ 3.1]",
        );
        check(
            "%f %f %F %F",
            vec![
                f(f64::INFINITY),
                f(f64::NEG_INFINITY),
                f(f64::NAN),
                f(f64::INFINITY),
            ],
            "inf -inf NAN INF",
        );
        check(
            "[%8f] [%-8f] [%08f] [%+f]",
            vec![f(f64::INFINITY); 4],
            "[     inf] [inf     ] [     inf] [+inf]",
        );
        check("%f", vec![f(-0.0)], "-0.000000");
        check("%.20f", vec![f(0.1)], "0.10000000000000000555");
        check("%.1100f", vec![f(1.0)], &format!("1.{}", "0".repeat(1100)));
        check(
            "%.800e",
            vec![f(1.0)],
            &format!("1.{}e+00", "0".repeat(800)),
        );
        // The largest double in %f has 309 integer digits.
        let (n, out) = run("%f", vec![f(f64::MAX)]);
        assert_eq!(n, 316);
        assert!(out.starts_with("179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.000000"));
    }

    #[test]
    fn floats_general() {
        check(
            "%g %g %g %g",
            vec![f(0.0), f(1.0), f(100000.0), f(1000000.0)],
            "0 1 100000 1e+06",
        );
        check(
            "%g %g %g",
            vec![f(0.0001), f(0.00001), f(123456789.0)],
            "0.0001 1e-05 1.23457e+08",
        );
        check(
            "%g %G %.3g %.0g %#g %#.3g",
            vec![f(3.14159), f(1e-10), f(3.14159), f(2.5), f(1.0), f(100.0)],
            "3.14159 1E-10 3.14 2 1.00000 100.",
        );
        check("%g %g", vec![f(99999.99), f(999999.5)], "100000 1e+06");
        check("%.10g %g", vec![f(0.1), f(1e100)], "0.1 1e+100");
        check("%g %g", vec![f(f64::NAN), f(-f64::INFINITY)], "nan -inf");
        check("%#g", vec![f(1e-10)], "1.00000e-10");
        check(
            "%.15g %.17g",
            vec![f(0.1), f(0.1)],
            "0.1 0.10000000000000001",
        );
    }

    #[test]
    fn floats_hex() {
        check("%a %A", vec![f(1.0), f(1.0)], "0x1p+0 0X1P+0");
        check(
            "%a %a %a",
            vec![f(0.0), f(-0.0), f(0.5)],
            "0x0p+0 -0x0p+0 0x1p-1",
        );
        check("%a %a", vec![f(1.5), f(255.0)], "0x1.8p+0 0x1.fep+7");
        check(
            "%.2a %.0a %.0a %#.0a",
            vec![f(1.0 / 3.0), f(1.5), f(2.5), f(1.0)],
            "0x1.55p-2 0x2p+0 0x1p+1 0x1.p+0",
        );
        check("%a", vec![f(f64::MIN_POSITIVE)], "0x1p-1022");
        check("%a", vec![f(f64::from_bits(1))], "0x1p-1074");
        check("%a", vec![f(f64::MAX)], "0x1.fffffffffffffp+1023");
        check("%.20a", vec![f(1.0)], "0x1.00000000000000000000p+0");
        check(
            "[%12a] [%-12a] [%012a]",
            vec![f(1.5); 3],
            "[    0x1.8p+0] [0x1.8p+0    ] [0x00001.8p+0]",
        );
        check("%a %a", vec![f(f64::INFINITY), f(f64::NAN)], "inf nan");
    }

    #[test]
    fn positional() {
        check("%2$s %1$s", vec![s("world"), s("hello")], "hello world");
        check("%2$d %1$d %2$d", vec![1, 2], "2 1 2");
        check("%1$*2$d|%3$.*4$f", vec![7, 5, f(3.14159), 2], "    7|3.14");
        check("%2$f %1$d", vec![5, f(1.5)], "1.500000 5");
        let (n, _) = run("%1$d %d", vec![1, 2]);
        assert_eq!(n, -1, "mixing positional and sequential is rejected");
        let (n, _) = run("%1$*d", vec![1, 2]);
        assert_eq!(n, -1, "a width from an unnumbered argument is rejected");
        // A literal '$' does not make the format positional.
        check("cost: $%d, %s", vec![5, s("ok")], "cost: $5, ok");
        check("$%2$d$%1$d$", vec![1, 2], "$2$1$");
    }

    #[test]
    fn huge_precision() {
        let (n, out) = run("%.1500e", vec![f(1.0)]);
        assert_eq!(n, 1506);
        assert!(out.starts_with("1.000") && out.ends_with("0e+00"));
        assert_eq!(out.len(), 1506);
        let (n, out) = run("%#.1500g", vec![f(1.5)]);
        assert_eq!(n, 1501);
        assert!(out.starts_with("1.5000") && out.ends_with("0"));
        check("%.1500g", vec![f(1.5)], "1.5");
        let (n, out) = run("%#.1500g", vec![f(1e100)]);
        assert_eq!(n, 1501, "fixed form: 101 integer digits and 1399 zeros");
        assert!(out.starts_with("10000") && out.ends_with("0"));
        let (n, out) = run("%#.1500g", vec![f(1e-10)]);
        assert_eq!(n, 1505);
        assert!(out.starts_with("1.000") && out.ends_with("0e-10"));
        let (n, out) = run("%.100a", vec![f(1.0)]);
        assert_eq!(n, 107);
        assert!(out.starts_with("0x1.000") && out.ends_with("0p+0"));
        let (n, out) = run("%.2000f", vec![f(0.5)]);
        assert_eq!(n, 2002);
        assert!(out.starts_with("0.500") && out.ends_with("0"));
        // Widths above INT_MAX are rejected rather than read as `*`.
        let (n, _) = run("%18446744073709551615d", vec![5]);
        assert_eq!(n, -1);
        let (n, _) = run("%3000000000d", vec![5]);
        assert_eq!(n, -1);
    }

    #[test]
    fn errors() {
        let (n, _) = run("%n", vec![0]);
        assert_eq!(n, -1);
        assert_eq!(Errno::get(), Errno::EINVAL);
        let (n, _) = run("%y", vec![0]);
        assert_eq!(n, -1);
        let (n, _) = run("%", vec![0]);
        assert_eq!(n, -1);
        let (n, _) = run("abc%", vec![0]);
        assert_eq!(n, -1);
    }

    #[test]
    fn snprintf_bounds() {
        let cfmt = c"%s=%d";
        let mut args = FakeArgs {
            words: vec![s("key"), 12345],
        };
        let mut buf = [0xffu8; 6];
        // SAFETY: valid buffer and matching arguments.
        let n = unsafe {
            vsnprintf(
                buf.as_mut_ptr() as *mut c_char,
                6,
                cfmt.as_ptr(),
                &mut args.list(),
            )
        };
        assert_eq!(n, 9);
        assert_eq!(&buf, b"key=1\0");
        // SAFETY: as above.
        let n = unsafe {
            vsnprintf(
                buf.as_mut_ptr() as *mut c_char,
                0,
                cfmt.as_ptr(),
                &mut args.list(),
            )
        };
        assert_eq!(n, 9);
        assert_eq!(&buf, b"key=1\0");
        let mut out: *mut c_char = ptr::null_mut();
        // SAFETY: as above.
        let n = unsafe { vasprintf(&mut out, cfmt.as_ptr(), &mut args.list()) };
        assert_eq!(n, 9);
        // SAFETY: NUL-terminated result.
        assert_eq!(
            unsafe { std::ffi::CStr::from_ptr(out) }.to_bytes(),
            b"key=12345"
        );
        // SAFETY: our block.
        unsafe { malloc::dealloc(out as *mut u8) };
    }
}
