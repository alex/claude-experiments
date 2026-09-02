//! `<iconv.h>` for the Unicode encodings (UTF-8, UTF-16, UTF-32 / UCS-4 /
//! `wchar_t`) plus ASCII and Latin-1: enough for C++ `codecvt` facets and
//! for programs that convert between the encodings this library itself
//! uses. Anything else fails with `EINVAL` at `iconv_open`.

use crate::c_char;
use crate::errno::Errno;
use crate::malloc;
use core::ffi::{c_int, c_void};
use core::ptr;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Enc {
    Utf8,
    Utf16Le,
    Utf16Be,
    Utf32Le,
    Utf32Be,
    Ascii,
    Latin1,
}

/// A conversion descriptor.
struct Cd {
    from: Enc,
    to: Enc,
}

/// Parses an encoding name, ignoring case, punctuation and `//` suffixes
/// such as `//TRANSLIT`.
fn parse_name(name: &[u8]) -> Option<Enc> {
    let name = name.split(|&b| b == b'/').next().unwrap_or(b"");
    let mut key = [0u8; 16];
    let mut n = 0;
    for &b in name {
        if b.is_ascii_alphanumeric() {
            if n == key.len() {
                return None;
            }
            key[n] = b.to_ascii_uppercase();
            n += 1;
        }
    }
    Some(match &key[..n] {
        b"UTF8" => Enc::Utf8,
        b"UTF16LE" | b"UCS2LE" => Enc::Utf16Le,
        b"UTF16BE" | b"UCS2BE" | b"UTF16" | b"UCS2" => Enc::Utf16Be,
        b"UTF32LE" | b"UCS4LE" | b"WCHART" => Enc::Utf32Le,
        b"UTF32BE" | b"UCS4BE" | b"UTF32" | b"UCS4" => Enc::Utf32Be,
        b"ASCII" | b"USASCII" | b"ANSIX341968" | b"646" => Enc::Ascii,
        b"ISO88591" | b"LATIN1" | b"L1" | b"CP819" => Enc::Latin1,
        _ => return None,
    })
}

/// `iconv_open(3)`.
///
/// # Safety
/// Both names must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn iconv_open(to: *const c_char, from: *const c_char) -> *mut c_void {
    // SAFETY: caller contract.
    let (to, from) = unsafe {
        (
            core::ffi::CStr::from_ptr(to).to_bytes(),
            core::ffi::CStr::from_ptr(from).to_bytes(),
        )
    };
    let (Some(to), Some(from)) = (parse_name(to), parse_name(from)) else {
        Errno::EINVAL.set();
        return usize::MAX as *mut c_void;
    };
    let cd = malloc::alloc(core::mem::size_of::<Cd>()) as *mut Cd;
    if cd.is_null() {
        return usize::MAX as *mut c_void;
    }
    // SAFETY: fresh block of the right size.
    unsafe { cd.write(Cd { from, to }) };
    cd as *mut c_void
}

/// `iconv_close(3)`.
///
/// # Safety
/// `cd` must come from [`iconv_open`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn iconv_close(cd: *mut c_void) -> c_int {
    if cd as usize == usize::MAX {
        Errno::EBADF.set();
        return -1;
    }
    // SAFETY: caller contract.
    unsafe { malloc::dealloc(cd as *mut u8) };
    0
}

/// Outcome of decoding one character.
enum Step {
    /// Code point and bytes consumed.
    Char(u32, usize),
    Incomplete,
    Invalid,
}

fn decode(enc: Enc, s: &[u8]) -> Step {
    match enc {
        Enc::Utf8 => {
            let Some(&b0) = s.first() else {
                return Step::Incomplete;
            };
            let (len, min, init) = match b0 {
                0x00..=0x7f => return Step::Char(b0 as u32, 1),
                0xc2..=0xdf => (2, 0x80, (b0 & 0x1f) as u32),
                0xe0..=0xef => (3, 0x800, (b0 & 0x0f) as u32),
                0xf0..=0xf4 => (4, 0x10000, (b0 & 0x07) as u32),
                _ => return Step::Invalid,
            };
            let mut cp = init;
            for i in 1..len {
                let Some(&b) = s.get(i) else {
                    return Step::Incomplete;
                };
                if b & 0xc0 != 0x80 {
                    return Step::Invalid;
                }
                cp = (cp << 6) | (b & 0x3f) as u32;
            }
            if cp < min || cp > 0x10ffff || (0xd800..=0xdfff).contains(&cp) {
                return Step::Invalid;
            }
            Step::Char(cp, len)
        }
        Enc::Utf16Le | Enc::Utf16Be => {
            let unit = |i: usize| -> Option<u32> {
                let (a, b) = (*s.get(2 * i)?, *s.get(2 * i + 1)?);
                Some(if enc == Enc::Utf16Le {
                    a as u32 | (b as u32) << 8
                } else {
                    (a as u32) << 8 | b as u32
                })
            };
            let Some(u0) = unit(0) else {
                return Step::Incomplete;
            };
            if (0xd800..0xdc00).contains(&u0) {
                let Some(u1) = unit(1) else {
                    return Step::Incomplete;
                };
                if !(0xdc00..0xe000).contains(&u1) {
                    return Step::Invalid;
                }
                Step::Char(0x10000 + ((u0 - 0xd800) << 10) + (u1 - 0xdc00), 4)
            } else if (0xdc00..0xe000).contains(&u0) {
                Step::Invalid
            } else {
                Step::Char(u0, 2)
            }
        }
        Enc::Utf32Le | Enc::Utf32Be => {
            if s.len() < 4 {
                return Step::Incomplete;
            }
            let bytes = [s[0], s[1], s[2], s[3]];
            let cp = if enc == Enc::Utf32Le {
                u32::from_le_bytes(bytes)
            } else {
                u32::from_be_bytes(bytes)
            };
            if cp > 0x10ffff || (0xd800..=0xdfff).contains(&cp) {
                return Step::Invalid;
            }
            Step::Char(cp, 4)
        }
        Enc::Ascii => match s.first() {
            None => Step::Incomplete,
            Some(&b) if b < 0x80 => Step::Char(b as u32, 1),
            Some(_) => Step::Invalid,
        },
        Enc::Latin1 => match s.first() {
            None => Step::Incomplete,
            Some(&b) => Step::Char(b as u32, 1),
        },
    }
}

/// Encodes `cp`; `None` if the encoding cannot represent it.
fn encode(enc: Enc, cp: u32, out: &mut [u8; 4]) -> Option<usize> {
    match enc {
        Enc::Utf8 => {
            let c = char::from_u32(cp)?;
            Some(c.encode_utf8(out).len())
        }
        Enc::Utf16Le | Enc::Utf16Be => {
            let c = char::from_u32(cp)?;
            let mut units = [0u16; 2];
            let n = c.encode_utf16(&mut units).len();
            for (i, u) in units[..n].iter().enumerate() {
                let b = if enc == Enc::Utf16Le {
                    u.to_le_bytes()
                } else {
                    u.to_be_bytes()
                };
                out[2 * i] = b[0];
                out[2 * i + 1] = b[1];
            }
            Some(2 * n)
        }
        Enc::Utf32Le | Enc::Utf32Be => {
            char::from_u32(cp)?;
            *out = if enc == Enc::Utf32Le {
                cp.to_le_bytes()
            } else {
                cp.to_be_bytes()
            };
            Some(4)
        }
        Enc::Ascii => {
            if cp < 0x80 {
                out[0] = cp as u8;
                Some(1)
            } else {
                None
            }
        }
        Enc::Latin1 => {
            if cp < 0x100 {
                out[0] = cp as u8;
                Some(1)
            } else {
                None
            }
        }
    }
}

/// `iconv(3)`.
///
/// # Safety
/// `cd` must come from [`iconv_open`]; the buffer pointers and lengths
/// must be valid or null as POSIX specifies.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn iconv(
    cd: *mut c_void,
    inbuf: *mut *mut c_char,
    inleft: *mut usize,
    outbuf: *mut *mut c_char,
    outleft: *mut usize,
) -> usize {
    if cd as usize == usize::MAX {
        Errno::EBADF.set();
        return usize::MAX;
    }
    // SAFETY: caller contract.
    let cd = unsafe { &*(cd as *const Cd) };
    // SAFETY: caller contract.
    if inbuf.is_null() || unsafe { *inbuf }.is_null() {
        // Stateless encodings: nothing to reset or flush.
        return 0;
    }
    // SAFETY: caller contract.
    let (mut ip, mut il, mut op, mut ol) =
        unsafe { (*inbuf as *const u8, *inleft, *outbuf as *mut u8, *outleft) };
    let result = loop {
        if il == 0 {
            break 0;
        }
        // SAFETY: `ip` is valid for `il` bytes.
        let input = unsafe { core::slice::from_raw_parts(ip, il) };
        let (cp, used) = match decode(cd.from, input) {
            Step::Char(cp, used) => (cp, used),
            Step::Incomplete => {
                Errno::EINVAL.set();
                break usize::MAX;
            }
            Step::Invalid => {
                Errno::EILSEQ.set();
                break usize::MAX;
            }
        };
        let mut buf = [0u8; 4];
        let Some(n) = encode(cd.to, cp, &mut buf) else {
            Errno::EILSEQ.set();
            break usize::MAX;
        };
        if n > ol {
            Errno::E2BIG.set();
            break usize::MAX;
        }
        // SAFETY: `op` has room for `n` bytes.
        unsafe { ptr::copy_nonoverlapping(buf.as_ptr(), op, n) };
        // SAFETY: advancing within the buffers.
        unsafe {
            op = op.add(n);
            ip = ip.add(used);
        }
        ol -= n;
        il -= used;
    };
    // SAFETY: caller contract.
    unsafe {
        *inbuf = ip as *mut c_char;
        *inleft = il;
        *outbuf = op as *mut c_char;
        *outleft = ol;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn convert(from: &str, to: &str, input: &[u8]) -> Result<Vec<u8>, i32> {
        let f = std::ffi::CString::new(from).unwrap();
        let t = std::ffi::CString::new(to).unwrap();
        // SAFETY: valid names and buffers.
        unsafe {
            let cd = iconv_open(t.as_ptr(), f.as_ptr());
            assert_ne!(cd as usize, usize::MAX);
            let mut out = vec![0u8; input.len() * 4 + 4];
            let mut ip = input.as_ptr() as *mut c_char;
            let mut il = input.len();
            let mut op = out.as_mut_ptr() as *mut c_char;
            let mut ol = out.len();
            let r = iconv(cd, &mut ip, &mut il, &mut op, &mut ol);
            iconv_close(cd);
            if r == usize::MAX {
                return Err(Errno::get().0);
            }
            out.truncate(out.len() - ol);
            Ok(out)
        }
    }

    #[test]
    fn round_trips() {
        let text = "héllo, wörld 😀";
        let wide = convert("UTF-8", "WCHAR_T", text.as_bytes()).unwrap();
        let expected: Vec<u8> = text
            .chars()
            .flat_map(|c| (c as u32).to_le_bytes())
            .collect();
        assert_eq!(wide, expected);
        assert_eq!(
            convert("UCS-4LE", "UTF-8//TRANSLIT", &wide).unwrap(),
            text.as_bytes()
        );
        let u16le = convert("utf8", "UTF-16LE", text.as_bytes()).unwrap();
        let expected: Vec<u8> = text.encode_utf16().flat_map(|u| u.to_le_bytes()).collect();
        assert_eq!(u16le, expected);
        assert_eq!(
            convert("UTF-16LE", "UTF-8", &u16le).unwrap(),
            text.as_bytes()
        );
        assert_eq!(
            convert("UTF-8", "ISO-8859-1", "hé".as_bytes()).unwrap(),
            b"h\xe9"
        );
        assert_eq!(
            convert("UTF-8", "ASCII", "hé".as_bytes()),
            Err(Errno::EILSEQ.0)
        );
        assert_eq!(convert("UTF-8", "UTF-8", b"\xff"), Err(Errno::EILSEQ.0));
        assert_eq!(convert("UTF-8", "UTF-8", b"\xe2\x82"), Err(Errno::EINVAL.0));
    }

    #[test]
    fn unknown_encoding() {
        // SAFETY: valid names.
        unsafe {
            assert_eq!(
                iconv_open(c"EBCDIC-US".as_ptr(), c"UTF-8".as_ptr()) as usize,
                usize::MAX
            );
            assert_eq!(Errno::get(), Errno::EINVAL);
        }
    }
}
