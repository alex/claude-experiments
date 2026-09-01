//! `<locale.h>` and `<langinfo.h>`.
//!
//! Only the C/POSIX locale semantics are implemented; the character
//! encoding is always UTF-8. `setlocale` accepts `C`, `POSIX`, `""` and
//! any name ending in `UTF-8`/`utf8`, and remembers the name so programs
//! that inspect it get back what they set.

use crate::c_char;
use crate::sync::Mutex;
use core::ffi::{c_int, c_void};
use core::ptr;

/// `struct lconv`.
#[allow(missing_docs)]
#[repr(C)]
pub struct Lconv {
    pub decimal_point: *mut c_char,
    pub thousands_sep: *mut c_char,
    pub grouping: *mut c_char,
    pub int_curr_symbol: *mut c_char,
    pub currency_symbol: *mut c_char,
    pub mon_decimal_point: *mut c_char,
    pub mon_thousands_sep: *mut c_char,
    pub mon_grouping: *mut c_char,
    pub positive_sign: *mut c_char,
    pub negative_sign: *mut c_char,
    pub int_frac_digits: c_char,
    pub frac_digits: c_char,
    pub p_cs_precedes: c_char,
    pub p_sep_by_space: c_char,
    pub n_cs_precedes: c_char,
    pub n_sep_by_space: c_char,
    pub p_sign_posn: c_char,
    pub n_sign_posn: c_char,
    pub int_p_cs_precedes: c_char,
    pub int_p_sep_by_space: c_char,
    pub int_n_cs_precedes: c_char,
    pub int_n_sep_by_space: c_char,
    pub int_p_sign_posn: c_char,
    pub int_n_sign_posn: c_char,
}

struct LconvCell(Lconv);
// SAFETY: the pointers refer to immutable static strings.
unsafe impl Sync for LconvCell {}

const EMPTY: *mut c_char = c"".as_ptr() as *mut c_char;

static C_LCONV: LconvCell = LconvCell(Lconv {
    decimal_point: c".".as_ptr() as *mut c_char,
    thousands_sep: EMPTY,
    grouping: EMPTY,
    int_curr_symbol: EMPTY,
    currency_symbol: EMPTY,
    mon_decimal_point: EMPTY,
    mon_thousands_sep: EMPTY,
    mon_grouping: EMPTY,
    positive_sign: EMPTY,
    negative_sign: EMPTY,
    int_frac_digits: c_char::MAX,
    frac_digits: c_char::MAX,
    p_cs_precedes: c_char::MAX,
    p_sep_by_space: c_char::MAX,
    n_cs_precedes: c_char::MAX,
    n_sep_by_space: c_char::MAX,
    p_sign_posn: c_char::MAX,
    n_sign_posn: c_char::MAX,
    int_p_cs_precedes: c_char::MAX,
    int_p_sep_by_space: c_char::MAX,
    int_n_cs_precedes: c_char::MAX,
    int_n_sep_by_space: c_char::MAX,
    int_p_sign_posn: c_char::MAX,
    int_n_sign_posn: c_char::MAX,
});

/// `localeconv(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn localeconv() -> *mut Lconv {
    &C_LCONV.0 as *const Lconv as *mut Lconv
}

/// The current locale name (NUL-terminated).
static NAME: Mutex<[u8; 64]> = Mutex::new(*b"C\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0");

fn is_supported(name: &[u8]) -> bool {
    name.is_empty()
        || name == b"C"
        || name == b"POSIX"
        || name.ends_with(b"UTF-8")
        || name.ends_with(b"utf8")
        || name.ends_with(b"UTF8")
        || name.ends_with(b"utf-8")
}

/// `setlocale(3)`.
///
/// # Safety
/// `locale` must be null or NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn setlocale(category: c_int, locale: *const c_char) -> *mut c_char {
    if !(0..=6).contains(&category) {
        return ptr::null_mut();
    }
    let mut name = NAME.lock();
    if locale.is_null() {
        return name.as_mut_ptr() as *mut c_char;
    }
    // SAFETY: caller contract.
    let mut requested = unsafe {
        core::slice::from_raw_parts(
            locale as *const u8,
            crate::string::search::strlen(locale as *const u8),
        )
    };
    let mut env_name = [0u8; 64];
    if requested.is_empty() {
        // From the environment: LC_ALL, then LANG.
        for var in [c"LC_ALL", c"LC_CTYPE", c"LANG"] {
            // SAFETY: NUL-terminated literal.
            let v = unsafe { crate::stdlib::env::getenv(var.as_ptr()) };
            if !v.is_null() {
                // SAFETY: getenv returns NUL-terminated strings.
                let s = unsafe {
                    core::slice::from_raw_parts(
                        v as *const u8,
                        crate::string::search::strlen(v as *const u8),
                    )
                };
                if !s.is_empty() {
                    let n = s.len().min(63);
                    env_name[..n].copy_from_slice(&s[..n]);
                    requested = &env_name[..n];
                    break;
                }
            }
        }
        if requested.is_empty() {
            requested = b"C";
        }
    }
    if !is_supported(requested) || requested.len() > 63 {
        return ptr::null_mut();
    }
    name[..requested.len()].copy_from_slice(requested);
    name[requested.len()] = 0;
    name.as_mut_ptr() as *mut c_char
}

/// `nl_langinfo(3)` for the C locale.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn nl_langinfo(item: c_int) -> *mut c_char {
    let s: &core::ffi::CStr = match item {
        14 => {
            let name = NAME.lock();
            let n = name.iter().position(|&b| b == 0).unwrap_or(0);
            if is_utf8(&name[..n]) {
                c"UTF-8"
            } else {
                c"ANSI_X3.4-1968"
            }
        }
        0x2002c => c"%a %b %e %H:%M:%S %Y", // D_T_FMT
        0x2002d => c"%m/%d/%y",             // D_FMT
        0x2002e => c"%H:%M:%S",             // T_FMT
        0x2002f => c"%I:%M:%S %p",          // T_FMT_AMPM
        0x20026 => c"AM",                   // AM_STR
        0x20027 => c"PM",                   // PM_STR
        0x10000 => c".",                    // RADIXCHAR
        0x10001 => c"",                     // THOUSEP
        0x50000 => c"^[yY]",                // YESEXPR
        0x50001 => c"^[nN]",                // NOEXPR
        0x40000 => c"",                     // CRNCYSTR
        _ => c"",
    };
    s.as_ptr() as *mut c_char
}

fn is_utf8(name: &[u8]) -> bool {
    !(name == b"C" || name == b"POSIX")
}

/// `locale_t` handles: an opaque non-null pointer is enough since there
/// is only one locale.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn newlocale(_mask: c_int, _name: *const c_char, _base: *mut c_void) -> *mut c_void {
    &C_LCONV as *const LconvCell as *mut c_void
}

/// `duplocale(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn duplocale(l: *mut c_void) -> *mut c_void {
    l
}

/// `freelocale(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn freelocale(_l: *mut c_void) {}

/// `uselocale(3)`: returns `LC_GLOBAL_LOCALE` (`(locale_t)-1`).
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn uselocale(_l: *mut c_void) -> *mut c_void {
    usize::MAX as *mut c_void
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CStr;

    #[test]
    fn locale_names() {
        // SAFETY: NUL-terminated literals.
        unsafe {
            assert_eq!(CStr::from_ptr(setlocale(6, ptr::null())).to_bytes(), b"C");
            assert!(!setlocale(6, c"C.UTF-8".as_ptr()).is_null());
            assert_eq!(
                CStr::from_ptr(setlocale(6, ptr::null())).to_bytes(),
                b"C.UTF-8"
            );
            assert_eq!(CStr::from_ptr(nl_langinfo(14)).to_bytes(), b"UTF-8");
            assert!(setlocale(6, c"xx_YY.ISO-8859-1".as_ptr()).is_null());
            assert!(setlocale(99, c"C".as_ptr()).is_null());
            assert!(!setlocale(0, c"POSIX".as_ptr()).is_null());
            assert_eq!(
                CStr::from_ptr(nl_langinfo(14)).to_bytes(),
                b"ANSI_X3.4-1968"
            );
            assert_eq!(
                CStr::from_ptr((*localeconv()).decimal_point).to_bytes(),
                b"."
            );
        }
    }
}
