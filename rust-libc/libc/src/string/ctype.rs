//! `<ctype.h>` for the C locale.
//!
//! Every function accepts `EOF` (-1) and values `0..=255`; other inputs
//! are undefined behaviour in C and simply classify as "none" here.

use core::ffi::c_int;

/// Converts the `int` argument to a byte if it is in the valid range.
#[inline(always)]
fn byte(c: c_int) -> Option<u8> {
    u8::try_from(c).ok()
}

macro_rules! classify {
    ($($(#[$doc:meta])* $name:ident => $pred:expr;)*) => {
        $(
            $(#[$doc])*
            #[cfg_attr(not(test), unsafe(no_mangle))]
            pub extern "C" fn $name(c: c_int) -> c_int {
                let pred: fn(u8) -> bool = $pred;
                byte(c).is_some_and(pred) as c_int
            }
        )*
    };
}

classify! {
    /// `isalpha(3)`.
    isalpha => |b| b.is_ascii_alphabetic();
    /// `isdigit(3)`.
    isdigit => |b| b.is_ascii_digit();
    /// `isalnum(3)`.
    isalnum => |b| b.is_ascii_alphanumeric();
    /// `isupper(3)`.
    isupper => |b| b.is_ascii_uppercase();
    /// `islower(3)`.
    islower => |b| b.is_ascii_lowercase();
    /// `isspace(3)`: space, `\t`, `\n`, `\v`, `\f`, `\r`.
    isspace => |b| matches!(b, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r');
    /// `isblank(3)`: space and tab.
    isblank => |b| matches!(b, b' ' | b'\t');
    /// `isxdigit(3)`.
    isxdigit => |b| b.is_ascii_hexdigit();
    /// `ispunct(3)`.
    ispunct => |b| b.is_ascii_punctuation();
    /// `isprint(3)`: printable including space.
    isprint => |b| (0x20..0x7f).contains(&b);
    /// `isgraph(3)`: printable excluding space.
    isgraph => |b| (0x21..0x7f).contains(&b);
    /// `iscntrl(3)`.
    iscntrl => |b| b < 0x20 || b == 0x7f;
    /// `isascii(3)`.
    isascii => |b| b < 0x80;
}

/// `toupper(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn toupper(c: c_int) -> c_int {
    match byte(c) {
        Some(b) if b.is_ascii_lowercase() => (b - 32) as c_int,
        _ => c,
    }
}

/// `tolower(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn tolower(c: c_int) -> c_int {
    match byte(c) {
        Some(b) if b.is_ascii_uppercase() => (b + 32) as c_int,
        _ => c,
    }
}

/// `toascii(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn toascii(c: c_int) -> c_int {
    c & 0x7f
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classes() {
        for c in -1..256 {
            let b = c as u8;
            let valid = c >= 0;
            assert_eq!(isalpha(c) != 0, valid && b.is_ascii_alphabetic());
            assert_eq!(isspace(c) != 0, valid && b" \t\n\x0b\x0c\r".contains(&b));
            assert_eq!(isprint(c) != 0, valid && (0x20..0x7f).contains(&b));
            assert_eq!(iscntrl(c) != 0, valid && (b < 0x20 || b == 0x7f));
            assert_eq!(ispunct(c) != 0, valid && b.is_ascii_punctuation());
            assert_eq!(isupper(c) != 0, valid && b.is_ascii_uppercase());
            assert_eq!(isxdigit(c) != 0, valid && b.is_ascii_hexdigit());
            assert_eq!(
                toupper(c),
                if valid && b.is_ascii_lowercase() {
                    c - 32
                } else {
                    c
                }
            );
            assert_eq!(
                tolower(c),
                if valid && b.is_ascii_uppercase() {
                    c + 32
                } else {
                    c
                }
            );
        }
        assert_eq!(isalpha(-1), 0);
        assert_eq!(isalpha(0x141), 0);
        assert_eq!(toupper(-1), -1);
        assert_eq!(isblank(b'\t' as c_int), 1);
        assert_eq!(isblank(b'\n' as c_int), 0);
    }
}
