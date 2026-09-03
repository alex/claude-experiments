//! `<wchar.h>` and `<wctype.h>`.
//!
//! The multibyte encoding is always UTF-8. `wchar_t` is a Unicode code
//! point (`int` on Linux). Character classification uses `core`'s
//! Unicode tables.

use crate::c_char;
use crate::errno::Errno;
use crate::malloc;
use core::ffi::{c_int, c_long, c_longlong, c_ulong, c_ulonglong};
use core::ptr;

/// `wchar_t`.
#[cfg(target_arch = "x86_64")]
pub type WChar = i32;
/// `wchar_t` (unsigned on AArch64).
#[cfg(not(target_arch = "x86_64"))]
pub type WChar = u32;
/// `wint_t`.
pub type WInt = u32;
/// `WEOF`.
pub const WEOF: WInt = u32::MAX;

/// `mbstate_t`: bits 0..21 hold the code point bits gathered so far,
/// bits 21..24 the total length of the sequence being decoded (0 in
/// the initial state) and bits 24..32 the number of continuation bytes
/// still expected.
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct MbState {
    state: u32,
}

impl MbState {
    fn remaining(&self) -> u32 {
        self.state >> 24
    }
    fn total(&self) -> u32 {
        (self.state >> 21) & 7
    }
    fn partial(&self) -> u32 {
        self.state & 0x1f_ffff
    }
    fn set(&mut self, remaining: u32, total: u32, partial: u32) {
        self.state = (remaining << 24) | (total << 21) | (partial & 0x1f_ffff);
    }
}

/// Outcome of decoding.
enum Decoded {
    /// A complete character and the bytes consumed from this call.
    Char(u32, usize),
    /// More input is needed (state updated).
    Incomplete,
    Invalid,
}

/// Decodes one UTF-8 character from `s`, continuing a partial sequence
/// stored in `st`. Only bytes of `s` are consumed; the state remembers
/// what earlier calls contributed.
fn decode(s: &[u8], st: &mut MbState) -> Decoded {
    let (mut need, mut cp, mut total) = (st.remaining(), st.partial(), st.total());
    let mut i = 0;
    if need == 0 {
        let Some(&b) = s.first() else {
            return Decoded::Incomplete;
        };
        i = 1;
        (need, cp, total) = match b {
            0x00..=0x7f => {
                st.set(0, 0, 0);
                return Decoded::Char(b as u32, 1);
            }
            0xc2..=0xdf => (1, (b & 0x1f) as u32, 2),
            0xe0..=0xef => (2, (b & 0x0f) as u32, 3),
            0xf0..=0xf4 => (3, (b & 0x07) as u32, 4),
            _ => return Decoded::Invalid,
        };
    }
    while need > 0 {
        let Some(&b) = s.get(i) else {
            st.set(need, total, cp);
            return Decoded::Incomplete;
        };
        if b & 0xc0 != 0x80 {
            st.set(0, 0, 0);
            return Decoded::Invalid;
        }
        cp = (cp << 6) | (b & 0x3f) as u32;
        need -= 1;
        i += 1;
    }
    st.set(0, 0, 0);
    let min = match total {
        2 => 0x80,
        3 => 0x800,
        _ => 0x10000,
    };
    // Reject overlong forms, surrogates and out-of-range values.
    if cp < min || (0xd800..=0xdfff).contains(&cp) || cp > 0x10ffff {
        return Decoded::Invalid;
    }
    Decoded::Char(cp, i)
}

/// Encodes `cp` as UTF-8 into `out` (at least 4 bytes). Returns the
/// length, or `None` for invalid code points.
fn encode(cp: u32, out: &mut [u8; 4]) -> Option<usize> {
    let c = char::from_u32(cp)?;
    Some(c.encode_utf8(out).len())
}

/// Internal state for the non-restartable functions.
static GLOBAL_STATE: crate::sync::Mutex<MbState> = crate::sync::Mutex::new(MbState { state: 0 });

/// `mbrtowc(3)`.
///
/// # Safety
/// `s` must be null or valid for `n` bytes; `pwc`/`ps` null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mbrtowc(
    pwc: *mut WChar,
    s: *const c_char,
    n: usize,
    ps: *mut MbState,
) -> usize {
    let mut local = GLOBAL_STATE.lock();
    let st: &mut MbState = if ps.is_null() {
        &mut local
    } else {
        // SAFETY: caller contract.
        unsafe { &mut *ps }
    };
    if s.is_null() {
        st.set(0, 0, 0);
        return 0;
    }
    if n == 0 {
        return usize::MAX - 1;
    }
    // SAFETY: caller contract.
    let bytes = unsafe { core::slice::from_raw_parts(s as *const u8, n) };
    match decode(bytes, st) {
        Decoded::Char(cp, len) => {
            if !pwc.is_null() {
                // SAFETY: caller contract.
                unsafe { *pwc = cp as WChar };
            }
            if cp == 0 { 0 } else { len }
        }
        Decoded::Incomplete => usize::MAX - 1,
        Decoded::Invalid => {
            Errno::EILSEQ.set();
            usize::MAX
        }
    }
}

/// `wcrtomb(3)`.
///
/// # Safety
/// `s` must be null or valid for `MB_CUR_MAX` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcrtomb(s: *mut c_char, wc: WChar, _ps: *mut MbState) -> usize {
    if s.is_null() {
        return 1;
    }
    let mut buf = [0u8; 4];
    match encode(wc as u32, &mut buf) {
        Some(n) => {
            // SAFETY: caller contract.
            unsafe { ptr::copy_nonoverlapping(buf.as_ptr(), s as *mut u8, n) };
            n
        }
        None => {
            Errno::EILSEQ.set();
            usize::MAX
        }
    }
}

/// `mbrlen(3)`.
///
/// # Safety
/// As for [`mbrtowc`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mbrlen(s: *const c_char, n: usize, ps: *mut MbState) -> usize {
    // SAFETY: forwarded.
    unsafe { mbrtowc(ptr::null_mut(), s, n, ps) }
}

/// `mbsinit(3)`.
///
/// # Safety
/// `ps` must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mbsinit(ps: *const MbState) -> c_int {
    // SAFETY: caller contract.
    (ps.is_null() || unsafe { (*ps).state } == 0) as c_int
}

/// `mbtowc(3)`.
///
/// # Safety
/// As for [`mbrtowc`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mbtowc(pwc: *mut WChar, s: *const c_char, n: usize) -> c_int {
    if s.is_null() {
        GLOBAL_STATE.lock().set(0, 0, 0);
        return 0; // UTF-8 is stateless
    }
    let mut st = MbState::default();
    // SAFETY: forwarded.
    match unsafe { mbrtowc(pwc, s, n, &mut st) } {
        usize::MAX | 0xffff_ffff_ffff_fffe => -1,
        n => n as c_int,
    }
}

/// `wctomb(3)`.
///
/// # Safety
/// As for [`wcrtomb`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wctomb(s: *mut c_char, wc: WChar) -> c_int {
    if s.is_null() {
        return 0;
    }
    // SAFETY: forwarded.
    match unsafe { wcrtomb(s, wc, ptr::null_mut()) } {
        usize::MAX => -1,
        n => n as c_int,
    }
}

/// `mblen(3)`.
///
/// # Safety
/// As for [`mbrtowc`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mblen(s: *const c_char, n: usize) -> c_int {
    // SAFETY: forwarded.
    unsafe { mbtowc(ptr::null_mut(), s, n) }
}

/// Shared implementation of `mbsrtowcs` and `mbsnrtowcs`: converts at
/// most `nms` bytes of `*src` into at most `n` wide characters (unlimited
/// when `dst` is null).
///
/// # Safety
/// `src` must be valid and point to a string readable for `nms` bytes or
/// up to its NUL; `dst` null or valid for `n` elements.
unsafe fn mbs_to_wcs(
    dst: *mut WChar,
    src: *mut *const c_char,
    nms: usize,
    n: usize,
    ps: *mut MbState,
) -> usize {
    let mut global;
    let st: &mut MbState = if ps.is_null() {
        global = GLOBAL_STATE.lock();
        &mut global
    } else {
        // SAFETY: caller contract.
        unsafe { &mut *ps }
    };
    // SAFETY: caller contract.
    let mut s = unsafe { *src } as *const u8;
    let mut left = nms;
    let mut count = 0usize;
    loop {
        if (!dst.is_null() && count >= n) || left == 0 {
            break;
        }
        // SAFETY: the string is readable for `left` bytes or to its NUL; at
        // most 4 bytes of a character are examined and the terminator stops
        // the decoder.
        let len = unsafe { crate::string::search::strnlen(s, left.min(4)) };
        // SAFETY: as above.
        let bytes = unsafe { core::slice::from_raw_parts(s, len.max(1)) };
        match decode(bytes, st) {
            Decoded::Char(cp, l) => {
                if !dst.is_null() {
                    // SAFETY: `count < n`.
                    unsafe { *dst.add(count) = cp as WChar };
                }
                if cp == 0 {
                    s = ptr::null();
                    break;
                }
                count += 1;
                left -= l;
                // SAFETY: inside the string.
                s = unsafe { s.add(l) };
            }
            Decoded::Incomplete if len < 4 && len == left => {
                // The byte limit cut a character; its prefix is in the state.
                // SAFETY: inside the string.
                s = unsafe { s.add(len) };
                break;
            }
            _ => {
                Errno::EILSEQ.set();
                // SAFETY: caller contract.
                unsafe { *src = s as *const c_char };
                return usize::MAX;
            }
        }
    }
    if !dst.is_null() {
        // SAFETY: caller contract.
        unsafe { *src = s as *const c_char };
    }
    count
}

/// `mbsrtowcs(3)`.
///
/// # Safety
/// `src` must be valid and point to a NUL-terminated string; `dst` null
/// or valid for `n` elements.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mbsrtowcs(
    dst: *mut WChar,
    src: *mut *const c_char,
    n: usize,
    ps: *mut MbState,
) -> usize {
    // SAFETY: forwarded.
    unsafe { mbs_to_wcs(dst, src, usize::MAX, n, ps) }
}

/// `mbsnrtowcs(3)`: like [`mbsrtowcs`] but reads at most `nms` bytes.
///
/// # Safety
/// As for [`mbsrtowcs`], with `nms` bounding the readable input.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mbsnrtowcs(
    dst: *mut WChar,
    src: *mut *const c_char,
    nms: usize,
    n: usize,
    ps: *mut MbState,
) -> usize {
    // SAFETY: forwarded.
    unsafe { mbs_to_wcs(dst, src, nms, n, ps) }
}

/// `mbstowcs(3)`.
///
/// # Safety
/// `src` must be NUL-terminated; `dst` null or valid for `n` elements.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mbstowcs(dst: *mut WChar, src: *const c_char, n: usize) -> usize {
    let mut p = src;
    // SAFETY: forwarded.
    unsafe { mbsrtowcs(dst, &mut p, n, ptr::null_mut()) }
}

/// Shared implementation of `wcsrtombs` and `wcsnrtombs`: converts at
/// most `nwc` wide characters of `*src` into at most `n` bytes (unlimited
/// when `dst` is null).
///
/// # Safety
/// `src` must be valid and point to a wide string readable for `nwc`
/// elements or up to its NUL; `dst` null or valid for `n` bytes.
unsafe fn wcs_to_mbs(dst: *mut c_char, src: *mut *const WChar, nwc: usize, n: usize) -> usize {
    // SAFETY: caller contract.
    let mut s = unsafe { *src };
    let mut left = nwc;
    let mut count = 0usize;
    let mut buf = [0u8; 4];
    while left > 0 {
        // SAFETY: the wide string is readable for `left` elements or to its NUL.
        let wc = unsafe { *s };
        let Some(len) = encode(wc as u32, &mut buf) else {
            Errno::EILSEQ.set();
            // SAFETY: caller contract.
            unsafe { *src = s };
            return usize::MAX;
        };
        if !dst.is_null() && count + len > n {
            break;
        }
        if !dst.is_null() {
            // SAFETY: room was checked.
            unsafe { ptr::copy_nonoverlapping(buf.as_ptr(), (dst as *mut u8).add(count), len) };
        }
        if wc == 0 {
            s = ptr::null();
            break;
        }
        count += len;
        left -= 1;
        // SAFETY: inside the string.
        s = unsafe { s.add(1) };
    }
    if !dst.is_null() {
        // SAFETY: caller contract.
        unsafe { *src = s };
    }
    count
}

/// `wcsrtombs(3)`.
///
/// # Safety
/// `src` must be valid and point to a NUL-terminated wide string; `dst`
/// null or valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcsrtombs(
    dst: *mut c_char,
    src: *mut *const WChar,
    n: usize,
    _ps: *mut MbState,
) -> usize {
    // SAFETY: forwarded.
    unsafe { wcs_to_mbs(dst, src, usize::MAX, n) }
}

/// `wcsnrtombs(3)`: like [`wcsrtombs`] but reads at most `nwc` elements.
///
/// # Safety
/// As for [`wcsrtombs`], with `nwc` bounding the readable input.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcsnrtombs(
    dst: *mut c_char,
    src: *mut *const WChar,
    nwc: usize,
    n: usize,
    _ps: *mut MbState,
) -> usize {
    // SAFETY: forwarded.
    unsafe { wcs_to_mbs(dst, src, nwc, n) }
}

/// `wcstombs(3)`.
///
/// # Safety
/// `src` must be NUL-terminated; `dst` null or valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcstombs(dst: *mut c_char, src: *const WChar, n: usize) -> usize {
    let mut p = src;
    // SAFETY: forwarded.
    unsafe { wcsrtombs(dst, &mut p, n, ptr::null_mut()) }
}

/// `btowc(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn btowc(c: c_int) -> WInt {
    if (0..0x80).contains(&c) {
        c as WInt
    } else {
        WEOF
    }
}

/// `wctob(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn wctob(c: WInt) -> c_int {
    if c < 0x80 { c as c_int } else { -1 }
}

// ---------------------------------------------------------------------
// Wide string functions.

/// Length of a NUL-terminated wide string.
///
/// # Safety
/// `s` must be NUL-terminated.
unsafe fn wlen(s: *const WChar) -> usize {
    let mut n = 0;
    // SAFETY: caller contract.
    while unsafe { *s.add(n) } != 0 {
        n += 1;
    }
    n
}

/// `wcslen(3)`.
///
/// # Safety
/// `s` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcslen(s: *const WChar) -> usize {
    // SAFETY: forwarded.
    unsafe { wlen(s) }
}

/// `wcsnlen(3)`.
///
/// # Safety
/// `s` must be readable up to the terminator or `n` elements.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcsnlen(s: *const WChar, n: usize) -> usize {
    let mut i = 0;
    // SAFETY: caller contract.
    while i < n && unsafe { *s.add(i) } != 0 {
        i += 1;
    }
    i
}

/// `wcscpy(3)`.
///
/// # Safety
/// `src` must be NUL-terminated; `dst` large enough.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcscpy(dst: *mut WChar, src: *const WChar) -> *mut WChar {
    // SAFETY: caller contract.
    unsafe {
        let n = wlen(src) + 1;
        ptr::copy_nonoverlapping(src, dst, n);
    }
    dst
}

/// `wcsncpy(3)`.
///
/// # Safety
/// `dst` must be valid for `n` elements.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcsncpy(dst: *mut WChar, src: *const WChar, n: usize) -> *mut WChar {
    // SAFETY: caller contract.
    unsafe {
        let len = wcsnlen(src, n);
        ptr::copy_nonoverlapping(src, dst, len);
        ptr::write_bytes(dst.add(len), 0, n - len);
    }
    dst
}

/// `wcscat(3)`.
///
/// # Safety
/// Both must be NUL-terminated; `dst` large enough.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcscat(dst: *mut WChar, src: *const WChar) -> *mut WChar {
    // SAFETY: caller contract.
    unsafe {
        wcscpy(dst.add(wlen(dst)), src);
    }
    dst
}

/// `wcsncat(3)`.
///
/// # Safety
/// `dst` must be NUL-terminated and large enough.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcsncat(dst: *mut WChar, src: *const WChar, n: usize) -> *mut WChar {
    // SAFETY: caller contract.
    unsafe {
        let d = wlen(dst);
        let s = wcsnlen(src, n);
        ptr::copy_nonoverlapping(src, dst.add(d), s);
        *dst.add(d + s) = 0;
    }
    dst
}

/// `wcscmp(3)`.
///
/// # Safety
/// Both must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcscmp(a: *const WChar, b: *const WChar) -> c_int {
    // SAFETY: forwarded.
    unsafe { wcsncmp(a, b, usize::MAX) }
}

/// `wcsncmp(3)`.
///
/// # Safety
/// Both must be NUL-terminated or readable for `n` elements.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcsncmp(a: *const WChar, b: *const WChar, n: usize) -> c_int {
    let mut i = 0;
    while i < n {
        // SAFETY: caller contract.
        let (x, y) = unsafe { (*a.add(i), *b.add(i)) };
        if x != y {
            return if (x as u32) < (y as u32) { -1 } else { 1 };
        }
        if x == 0 {
            return 0;
        }
        i += 1;
    }
    0
}

/// `wcscoll(3)`: `wcscmp` in the C locale.
///
/// # Safety
/// Both must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcscoll(a: *const WChar, b: *const WChar) -> c_int {
    // SAFETY: forwarded.
    unsafe { wcscmp(a, b) }
}

/// `wcsxfrm(3)`.
///
/// # Safety
/// `src` NUL-terminated; `dst` valid for `n` elements.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcsxfrm(dst: *mut WChar, src: *const WChar, n: usize) -> usize {
    // SAFETY: caller contract.
    unsafe {
        let len = wlen(src);
        if n > len {
            ptr::copy_nonoverlapping(src, dst, len + 1);
        }
        len
    }
}

/// `wcscasecmp(3)`.
///
/// # Safety
/// Both must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcscasecmp(a: *const WChar, b: *const WChar) -> c_int {
    // SAFETY: forwarded.
    unsafe { wcsncasecmp(a, b, usize::MAX) }
}

/// `wcsncasecmp(3)`.
///
/// # Safety
/// Both must be NUL-terminated or readable for `n` elements.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcsncasecmp(a: *const WChar, b: *const WChar, n: usize) -> c_int {
    let mut i = 0;
    while i < n {
        // SAFETY: caller contract.
        let (x, y) = unsafe { (towlower(*a.add(i) as WInt), towlower(*b.add(i) as WInt)) };
        if x != y {
            return if x < y { -1 } else { 1 };
        }
        if x == 0 {
            return 0;
        }
        i += 1;
    }
    0
}

/// `wcschr(3)`.
///
/// # Safety
/// `s` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcschr(s: *const WChar, c: WChar) -> *mut WChar {
    let mut i = 0;
    loop {
        // SAFETY: caller contract.
        let x = unsafe { *s.add(i) };
        if x == c {
            // SAFETY: inside the string.
            return unsafe { s.add(i) as *mut WChar };
        }
        if x == 0 {
            return ptr::null_mut();
        }
        i += 1;
    }
}

/// `wcsrchr(3)`.
///
/// # Safety
/// `s` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcsrchr(s: *const WChar, c: WChar) -> *mut WChar {
    // SAFETY: caller contract.
    let n = unsafe { wlen(s) };
    for i in (0..=n).rev() {
        // SAFETY: inside the string.
        if unsafe { *s.add(i) } == c {
            // SAFETY: as above.
            return unsafe { s.add(i) as *mut WChar };
        }
    }
    ptr::null_mut()
}

/// `wmemchr(3)`.
///
/// # Safety
/// `s` must be valid for `n` elements.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wmemchr(s: *const WChar, c: WChar, n: usize) -> *mut WChar {
    for i in 0..n {
        // SAFETY: caller contract.
        if unsafe { *s.add(i) } == c {
            // SAFETY: inside the buffer.
            return unsafe { s.add(i) as *mut WChar };
        }
    }
    ptr::null_mut()
}

/// `wmemcmp(3)`.
///
/// # Safety
/// Both must be valid for `n` elements.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wmemcmp(a: *const WChar, b: *const WChar, n: usize) -> c_int {
    for i in 0..n {
        // SAFETY: caller contract.
        let (x, y) = unsafe { (*a.add(i), *b.add(i)) };
        if x != y {
            return if (x as u32) < (y as u32) { -1 } else { 1 };
        }
    }
    0
}

/// `wmemcpy(3)`.
///
/// # Safety
/// Both must be valid for `n` elements and not overlap.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wmemcpy(dst: *mut WChar, src: *const WChar, n: usize) -> *mut WChar {
    // SAFETY: caller contract.
    unsafe { ptr::copy_nonoverlapping(src, dst, n) };
    dst
}

/// `wmemmove(3)`.
///
/// # Safety
/// Both must be valid for `n` elements.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wmemmove(dst: *mut WChar, src: *const WChar, n: usize) -> *mut WChar {
    // SAFETY: caller contract.
    unsafe { ptr::copy(src, dst, n) };
    dst
}

/// `wmemset(3)`.
///
/// # Safety
/// `dst` must be valid for `n` elements.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wmemset(dst: *mut WChar, c: WChar, n: usize) -> *mut WChar {
    for i in 0..n {
        // SAFETY: caller contract.
        unsafe { *dst.add(i) = c };
    }
    dst
}

/// `wcsstr(3)`.
///
/// # Safety
/// Both must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcsstr(hay: *const WChar, needle: *const WChar) -> *mut WChar {
    // SAFETY: caller contract.
    let (h, n) = unsafe {
        (
            core::slice::from_raw_parts(hay, wlen(hay)),
            core::slice::from_raw_parts(needle, wlen(needle)),
        )
    };
    if n.is_empty() {
        return hay as *mut WChar;
    }
    match h.windows(n.len()).position(|w| w == n) {
        // SAFETY: inside the string.
        Some(i) => unsafe { hay.add(i) as *mut WChar },
        None => ptr::null_mut(),
    }
}

/// `wcsspn(3)`.
///
/// # Safety
/// Both must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcsspn(s: *const WChar, accept: *const WChar) -> usize {
    let mut i = 0;
    // SAFETY: caller contract.
    unsafe {
        while *s.add(i) != 0 && !wcschr(accept, *s.add(i)).is_null() {
            i += 1;
        }
    }
    i
}

/// `wcscspn(3)`.
///
/// # Safety
/// Both must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcscspn(s: *const WChar, reject: *const WChar) -> usize {
    let mut i = 0;
    // SAFETY: caller contract.
    unsafe {
        while *s.add(i) != 0 && wcschr(reject, *s.add(i)).is_null() {
            i += 1;
        }
    }
    i
}

/// `wcspbrk(3)`.
///
/// # Safety
/// Both must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcspbrk(s: *const WChar, accept: *const WChar) -> *mut WChar {
    // SAFETY: caller contract.
    unsafe {
        let p = s.add(wcscspn(s, accept));
        if *p != 0 {
            p as *mut WChar
        } else {
            ptr::null_mut()
        }
    }
}

/// `wcstok(3)`.
///
/// # Safety
/// As for `strtok_r`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcstok(
    s: *mut WChar,
    delim: *const WChar,
    save: *mut *mut WChar,
) -> *mut WChar {
    // SAFETY: caller contract.
    unsafe {
        let mut s = if s.is_null() { *save } else { s };
        if s.is_null() {
            return ptr::null_mut();
        }
        s = s.add(wcsspn(s, delim));
        if *s == 0 {
            *save = ptr::null_mut();
            return ptr::null_mut();
        }
        let token = s;
        s = s.add(wcscspn(s, delim));
        if *s != 0 {
            *s = 0;
            *save = s.add(1);
        } else {
            *save = ptr::null_mut();
        }
        token
    }
}

/// `wcsdup(3)`.
///
/// # Safety
/// `s` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcsdup(s: *const WChar) -> *mut WChar {
    // SAFETY: caller contract.
    unsafe {
        let n = wlen(s) + 1;
        let p = malloc::alloc(n * 4) as *mut WChar;
        if !p.is_null() {
            ptr::copy_nonoverlapping(s, p, n);
        }
        p
    }
}

/// `wcwidth(3)`: 0 for NUL and combining marks, -1 for controls, 2 for
/// East Asian wide/fullwidth ranges, 1 otherwise.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn wcwidth(c: WChar) -> c_int {
    let Some(ch) = char::from_u32(c as u32) else {
        return -1;
    };
    if c == 0 {
        return 0;
    }
    if ch.is_control() {
        return -1;
    }
    let cp = c as u32;
    // Combining marks (the common blocks).
    if matches!(cp, 0x0300..=0x036f | 0x0483..=0x0489 | 0x0591..=0x05bd | 0x0610..=0x061a | 0x064b..=0x065f | 0x1ab0..=0x1aff | 0x1dc0..=0x1dff | 0x20d0..=0x20ff | 0xfe20..=0xfe2f | 0x200b..=0x200f)
    {
        return 0;
    }
    // East Asian wide and fullwidth.
    if matches!(cp, 0x1100..=0x115f | 0x2e80..=0x303e | 0x3041..=0x33ff | 0x3400..=0x4dbf | 0x4e00..=0x9fff | 0xa000..=0xa4cf | 0xac00..=0xd7a3 | 0xf900..=0xfaff | 0xfe30..=0xfe4f | 0xff00..=0xff60 | 0xffe0..=0xffe6 | 0x1f300..=0x1f64f | 0x1f900..=0x1f9ff | 0x20000..=0x2fffd | 0x30000..=0x3fffd)
    {
        return 2;
    }
    1
}

/// `wcswidth(3)`.
///
/// # Safety
/// `s` must be valid for `n` elements or NUL-terminated within them.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcswidth(s: *const WChar, n: usize) -> c_int {
    let mut total = 0;
    for i in 0..n {
        // SAFETY: caller contract.
        let c = unsafe { *s.add(i) };
        if c == 0 {
            break;
        }
        let w = wcwidth(c);
        if w < 0 {
            return -1;
        }
        total += w;
    }
    total
}

/// Copies the ASCII prefix of a wide string (all a number can consist
/// of) into a narrow NUL-terminated buffer so the `strto*` family can
/// parse it. Short prefixes use `stack`; longer ones are `malloc`ed and
/// the flag says so. If that fails the prefix is truncated to the stack
/// buffer.
///
/// # Safety
/// `s` must be NUL-terminated.
unsafe fn narrow_prefix(s: *const WChar, stack: &mut [u8; 128]) -> (*mut u8, bool) {
    let mut n = 0;
    // SAFETY: caller contract; stops at the terminator.
    while (0..0x80).contains(&unsafe { *s.add(n) }) && unsafe { *s.add(n) } != 0 {
        n += 1;
    }
    let (buf, owned) = if n < stack.len() {
        (stack.as_mut_ptr(), false)
    } else {
        let p = crate::malloc::alloc(n + 1);
        if p.is_null() {
            n = stack.len() - 1;
            (stack.as_mut_ptr(), false)
        } else {
            (p, true)
        }
    };
    for i in 0..n {
        // SAFETY: `i < n` characters were checked to be ASCII, and the
        // buffer holds `n + 1` bytes.
        unsafe { *buf.add(i) = *s.add(i) as u8 };
    }
    // SAFETY: as above.
    unsafe { *buf.add(n) = 0 };
    (buf, owned)
}

macro_rules! wide_strto {
    ($($(#[$doc:meta])* $name:ident => $narrow:path, $ret:ty, $($base:ident)?;)*) => {
        $(
            $(#[$doc])*
            ///
            /// # Safety
            /// `s` must be NUL-terminated; `end` null or valid.
            #[cfg_attr(not(test), unsafe(no_mangle))]
            pub unsafe extern "C" fn $name(s: *const WChar, end: *mut *mut WChar $(, $base: c_int)?) -> $ret {
                let mut stack = [0u8; 128];
                // SAFETY: forwarded.
                let (buf, owned) = unsafe { narrow_prefix(s, &mut stack) };
                let mut e: *mut c_char = ptr::null_mut();
                // SAFETY: the buffer is NUL-terminated.
                let v = unsafe { $narrow(buf as *const c_char, &mut e $(, $base)?) };
                if !end.is_null() {
                    let consumed = e as usize - buf as usize;
                    // SAFETY: caller contract; `consumed` characters were ASCII.
                    unsafe { *end = s.add(consumed) as *mut WChar };
                }
                if owned {
                    // SAFETY: our block.
                    unsafe { crate::malloc::dealloc(buf) };
                }
                v
            }
        )*
    };
}

wide_strto! {
    /// `wcstol(3)`.
    wcstol => crate::stdlib::num::strtol, c_long, base;
    /// `wcstoul(3)`.
    wcstoul => crate::stdlib::num::strtoul, c_ulong, base;
    /// `wcstoll(3)`.
    wcstoll => crate::stdlib::num::strtoll, c_longlong, base;
    /// `wcstoull(3)`.
    wcstoull => crate::stdlib::num::strtoull, c_ulonglong, base;
    /// `wcstod(3)`.
    wcstod => crate::stdlib::num::strtod, f64,;
    /// `wcstof(3)`.
    wcstof => crate::stdlib::num::strtof, f32,;
}

// ---------------------------------------------------------------------
// wctype.

fn ch(c: WInt) -> Option<char> {
    char::from_u32(c)
}

macro_rules! wclass {
    ($($(#[$doc:meta])* $name:ident => $pred:expr;)*) => {
        $(
            $(#[$doc])*
            #[cfg_attr(not(test), unsafe(no_mangle))]
            pub extern "C" fn $name(c: WInt) -> c_int {
                let pred: fn(char) -> bool = $pred;
                ch(c).is_some_and(pred) as c_int
            }
        )*
    };
}

wclass! {
    /// `iswalpha(3)`.
    iswalpha => |c| c.is_alphabetic();
    /// `iswdigit(3)`: only the ASCII digits, as C requires.
    iswdigit => |c| c.is_ascii_digit();
    /// `iswalnum(3)`.
    iswalnum => |c| c.is_alphabetic() || c.is_numeric();
    /// `iswupper(3)`.
    iswupper => |c| c.is_uppercase();
    /// `iswlower(3)`.
    iswlower => |c| c.is_lowercase();
    /// `iswspace(3)`.
    iswspace => |c| c.is_whitespace();
    /// `iswblank(3)`.
    iswblank => |c| c == ' ' || c == '\t' || (c.is_whitespace() && !matches!(c, '\n' | '\r' | '\x0b' | '\x0c') && c as u32 >= 0x80 && c != '\u{2028}' && c != '\u{2029}' && c != '\u{85}');
    /// `iswcntrl(3)`.
    iswcntrl => |c| c.is_control();
    /// `iswprint(3)`.
    iswprint => |c| !c.is_control();
    /// `iswgraph(3)`.
    iswgraph => |c| !c.is_control() && !c.is_whitespace();
    /// `iswpunct(3)`.
    iswpunct => |c| !c.is_control() && !c.is_whitespace() && !c.is_alphanumeric();
    /// `iswxdigit(3)`.
    iswxdigit => |c| c.is_ascii_hexdigit();
}

/// `towupper(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn towupper(c: WInt) -> WInt {
    match ch(c) {
        Some(x) => {
            let mut up = x.to_uppercase();
            match (up.next(), up.next()) {
                (Some(u), None) => u as WInt,
                _ => c,
            }
        }
        None => c,
    }
}

/// `towlower(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn towlower(c: WInt) -> WInt {
    match ch(c) {
        Some(x) => {
            let mut lo = x.to_lowercase();
            match (lo.next(), lo.next()) {
                (Some(l), None) => l as WInt,
                _ => c,
            }
        }
        None => c,
    }
}

/// Character classes for `wctype`/`iswctype`.
static CLASSES: [(&[u8], extern "C" fn(WInt) -> c_int); 12] = [
    (b"alnum", iswalnum),
    (b"alpha", iswalpha),
    (b"blank", iswblank),
    (b"cntrl", iswcntrl),
    (b"digit", iswdigit),
    (b"graph", iswgraph),
    (b"lower", iswlower),
    (b"print", iswprint),
    (b"punct", iswpunct),
    (b"space", iswspace),
    (b"upper", iswupper),
    (b"xdigit", iswxdigit),
];

/// `wctype(3)`: returns 1-based class index, 0 if unknown.
///
/// # Safety
/// `name` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wctype(name: *const c_char) -> c_ulong {
    // SAFETY: caller contract.
    let n = unsafe {
        core::slice::from_raw_parts(
            name as *const u8,
            crate::string::search::strlen(name as *const u8),
        )
    };
    CLASSES
        .iter()
        .position(|(c, _)| *c == n)
        .map_or(0, |i| i as c_ulong + 1)
}

/// `iswctype(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn iswctype(c: WInt, class: c_ulong) -> c_int {
    match class {
        0 => 0,
        i if (i as usize) <= CLASSES.len() => (CLASSES[i as usize - 1].1)(c),
        _ => 0,
    }
}

/// `wctrans(3)`: 1 = tolower, 2 = toupper.
///
/// # Safety
/// `name` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wctrans(name: *const c_char) -> c_ulong {
    // SAFETY: caller contract.
    let n = unsafe {
        core::slice::from_raw_parts(
            name as *const u8,
            crate::string::search::strlen(name as *const u8),
        )
    };
    match n {
        b"tolower" => 1,
        b"toupper" => 2,
        _ => 0,
    }
}

/// `towctrans(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn towctrans(c: WInt, trans: c_ulong) -> WInt {
    match trans {
        1 => towlower(c),
        2 => towupper(c),
        _ => c,
    }
}

// ---------------------------------------------------------------------
// Wide stdio (byte streams with UTF-8 conversion).

use crate::stdio::File;

/// `fputwc(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fputwc(c: WChar, f: *mut File) -> WInt {
    let mut buf = [0u8; 4];
    let Some(n) = encode(c as u32, &mut buf) else {
        Errno::EILSEQ.set();
        return WEOF;
    };
    // SAFETY: forwarded.
    let mut g = unsafe { crate::stdio::lock(f) };
    if g.write_bytes(&buf[..n]).is_ok() {
        c as WInt
    } else {
        WEOF
    }
}

/// `putwc(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn putwc(c: WChar, f: *mut File) -> WInt {
    // SAFETY: forwarded.
    unsafe { fputwc(c, f) }
}

/// `putwchar(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn putwchar(c: WChar) -> WInt {
    // SAFETY: stdout is always valid.
    unsafe { fputwc(c, crate::stdio::stdout) }
}

/// `fputws(3)`.
///
/// # Safety
/// `s` NUL-terminated; `f` a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fputws(s: *const WChar, f: *mut File) -> c_int {
    // SAFETY: forwarded.
    let mut g = unsafe { crate::stdio::lock(f) };
    let mut i = 0;
    loop {
        // SAFETY: caller contract.
        let c = unsafe { *s.add(i) };
        if c == 0 {
            return 0;
        }
        let mut buf = [0u8; 4];
        let Some(n) = encode(c as u32, &mut buf) else {
            Errno::EILSEQ.set();
            return -1;
        };
        if g.write_bytes(&buf[..n]).is_err() {
            return -1;
        }
        i += 1;
    }
}

/// `fgetwc(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fgetwc(f: *mut File) -> WInt {
    // SAFETY: forwarded.
    let mut g = unsafe { crate::stdio::lock(f) };
    let mut st = MbState::default();
    let mut n = 0;
    loop {
        let Some(b) = g.getc() else { return WEOF };
        n += 1;
        // Feed one byte at a time; the state carries the partial value.
        match decode(&[b], &mut st) {
            Decoded::Char(c, _) => return c,
            Decoded::Incomplete if n < 4 => {}
            _ => {
                Errno::EILSEQ.set();
                return WEOF;
            }
        }
    }
}

/// `getwc(3)`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getwc(f: *mut File) -> WInt {
    // SAFETY: forwarded.
    unsafe { fgetwc(f) }
}

/// `getwchar(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn getwchar() -> WInt {
    // SAFETY: stdin is always valid.
    unsafe { fgetwc(crate::stdio::stdin) }
}

/// `fgetws(3)`.
///
/// # Safety
/// `s` valid for `n` elements; `f` a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fgetws(s: *mut WChar, n: c_int, f: *mut File) -> *mut WChar {
    if n <= 0 {
        return ptr::null_mut();
    }
    let mut i = 0usize;
    while i + 1 < n as usize {
        // SAFETY: forwarded.
        let c = unsafe { fgetwc(f) };
        if c == WEOF {
            break;
        }
        // SAFETY: `i + 1 < n`.
        unsafe { *s.add(i) = c as WChar };
        i += 1;
        if c == b'\n' as WInt {
            break;
        }
    }
    if i == 0 {
        return ptr::null_mut();
    }
    // SAFETY: `i < n`.
    unsafe { *s.add(i) = 0 };
    s
}

/// `fwide(3)`: streams are never oriented here.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn fwide(_f: *mut File, _mode: c_int) -> c_int {
    0
}

/// `vswprintf(3)`: formats through the byte `printf` and converts.
///
/// # Safety
/// `out` valid for `n` elements; `fmt` NUL-terminated wide string with
/// matching arguments.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vswprintf(
    out: *mut WChar,
    n: usize,
    fmt: *const WChar,
    ap: *mut crate::arch::va::VaList,
) -> c_int {
    // Narrow the format (it is UTF-8 text with ASCII conversions).
    let mut nfmt = [0u8; 1024];
    // SAFETY: caller contract.
    let flen = unsafe { wcstombs(nfmt.as_mut_ptr() as *mut c_char, fmt, nfmt.len() - 1) };
    if flen == usize::MAX || flen >= nfmt.len() - 1 {
        Errno::EOVERFLOW.set();
        return -1;
    }
    nfmt[flen] = 0;
    let mut bytes = [0u8; 4096];
    // SAFETY: the buffers are valid.
    let r = unsafe {
        crate::stdio::printf::vsnprintf(
            bytes.as_mut_ptr() as *mut c_char,
            bytes.len(),
            nfmt.as_ptr() as *const c_char,
            ap,
        )
    };
    if r < 0 || r as usize >= bytes.len() {
        return -1;
    }
    // SAFETY: the byte buffer is NUL-terminated.
    let count = unsafe { mbstowcs(out, bytes.as_ptr() as *const c_char, n) };
    if count == usize::MAX || count >= n {
        Errno::EOVERFLOW.set();
        return -1;
    }
    // SAFETY: `count < n`.
    unsafe { *out.add(count) = 0 };
    count as c_int
}

/// Narrows a wide format string (UTF-8 text with ASCII conversions) for
/// the byte-oriented printf/scanf engines. Returns false if it does not
/// fit.
///
/// # Safety
/// `fmt` must be NUL-terminated.
unsafe fn narrow_format(fmt: *const WChar, out: &mut [u8; 1024]) -> bool {
    // SAFETY: caller contract.
    let flen = unsafe { wcstombs(out.as_mut_ptr() as *mut c_char, fmt, out.len() - 1) };
    if flen == usize::MAX || flen >= out.len() - 1 {
        Errno::EOVERFLOW.set();
        return false;
    }
    out[flen] = 0;
    true
}

/// `vfwprintf(3)`: wide streams hold UTF-8, so the byte engine does the
/// work after the format is narrowed. The return value counts bytes, not
/// wide characters (a deviation for non-ASCII output).
///
/// # Safety
/// `f` valid; `fmt` NUL-terminated with matching arguments.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vfwprintf(
    f: *mut crate::stdio::File,
    fmt: *const WChar,
    ap: *mut crate::arch::va::VaList,
) -> c_int {
    let mut nfmt = [0u8; 1024];
    // SAFETY: forwarded.
    if !unsafe { narrow_format(fmt, &mut nfmt) } {
        return -1;
    }
    // SAFETY: forwarded.
    unsafe { crate::stdio::printf::vfprintf(f, nfmt.as_ptr() as *const c_char, ap) }
}

/// `vwprintf(3)`.
///
/// # Safety
/// As for [`vfwprintf`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vwprintf(fmt: *const WChar, ap: *mut crate::arch::va::VaList) -> c_int {
    // SAFETY: forwarded.
    unsafe { vfwprintf(crate::stdio::stdout, fmt, ap) }
}

/// `vfwscanf(3)`: like [`vfwprintf`], through the byte engine. `%n`
/// counts bytes.
///
/// # Safety
/// `f` valid; `fmt` NUL-terminated with matching arguments.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vfwscanf(
    f: *mut crate::stdio::File,
    fmt: *const WChar,
    ap: *mut crate::arch::va::VaList,
) -> c_int {
    let mut nfmt = [0u8; 1024];
    // SAFETY: forwarded.
    if !unsafe { narrow_format(fmt, &mut nfmt) } {
        return -1;
    }
    // SAFETY: forwarded.
    unsafe { crate::stdio::scanf::vfscanf(f, nfmt.as_ptr() as *const c_char, ap) }
}

/// `vwscanf(3)`.
///
/// # Safety
/// As for [`vfwscanf`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vwscanf(fmt: *const WChar, ap: *mut crate::arch::va::VaList) -> c_int {
    // SAFETY: forwarded.
    unsafe { vfwscanf(crate::stdio::stdin, fmt, ap) }
}

/// `vswscanf(3)`.
///
/// # Safety
/// `s` and `fmt` NUL-terminated; arguments match the format.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn vswscanf(
    s: *const WChar,
    fmt: *const WChar,
    ap: *mut crate::arch::va::VaList,
) -> c_int {
    let mut nfmt = [0u8; 1024];
    // SAFETY: forwarded.
    if !unsafe { narrow_format(fmt, &mut nfmt) } {
        return -1;
    }
    // SAFETY: caller contract.
    let len = unsafe { wcslen(s) };
    let Some(cap) = len.checked_mul(4).and_then(|v| v.checked_add(1)) else {
        Errno::EOVERFLOW.set();
        return -1;
    };
    let buf = crate::malloc::alloc(cap);
    if buf.is_null() {
        return -1;
    }
    // SAFETY: `buf` has room for the longest encoding plus the NUL.
    let n = unsafe { wcstombs(buf as *mut c_char, s, cap - 1) };
    if n == usize::MAX {
        // SAFETY: our block.
        unsafe { crate::malloc::dealloc(buf) };
        return -1;
    }
    // SAFETY: `n < cap`.
    unsafe { *buf.add(n) = 0 };
    // SAFETY: both buffers are NUL-terminated.
    let r = unsafe {
        crate::stdio::scanf::vsscanf(buf as *const c_char, nfmt.as_ptr() as *const c_char, ap)
    };
    // SAFETY: our block.
    unsafe { crate::malloc::dealloc(buf) };
    r
}

/// `ungetwc(3)`: pushes back the UTF-8 encoding of `wc`.
///
/// # Safety
/// `f` must be a valid stream.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn ungetwc(wc: WInt, f: *mut crate::stdio::File) -> WInt {
    if wc == WEOF {
        return WEOF;
    }
    let mut bytes = [0u8; 4];
    // SAFETY: the buffer holds any encoding.
    let n = unsafe {
        wcrtomb(
            bytes.as_mut_ptr() as *mut c_char,
            wc as WChar,
            core::ptr::null_mut(),
        )
    };
    if n == usize::MAX {
        return WEOF;
    }
    for &b in bytes[..n].iter().rev() {
        // SAFETY: forwarded.
        if unsafe { crate::stdio::ungetc(b as c_int, f) } == crate::stdio::EOF {
            return WEOF;
        }
    }
    wc
}

/// `wcsftime(3)`, through `strftime`.
///
/// # Safety
/// `out` valid for `max` elements; `fmt` NUL-terminated; `tm` valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn wcsftime(
    out: *mut WChar,
    max: usize,
    fmt: *const WChar,
    tm: *const crate::time::Tm,
) -> usize {
    let mut nfmt = [0u8; 1024];
    // SAFETY: forwarded.
    if !unsafe { narrow_format(fmt, &mut nfmt) } {
        return 0;
    }
    let mut bytes = [0u8; 4096];
    // SAFETY: the buffers are valid.
    let n = unsafe {
        crate::time::strftime::strftime(
            bytes.as_mut_ptr() as *mut c_char,
            bytes.len(),
            nfmt.as_ptr() as *const c_char,
            tm,
        )
    };
    if n == 0 {
        return 0;
    }
    // SAFETY: `strftime` NUL-terminated its output.
    let count = unsafe { mbstowcs(out, bytes.as_ptr() as *const c_char, max) };
    if count == usize::MAX || count >= max {
        return 0;
    }
    // SAFETY: `count < max`.
    unsafe { *out.add(count) = 0 };
    count
}

#[cfg(not(test))]
mod stubs {
    use crate::arch::va::variadic_stub;
    variadic_stub!(swprintf, 3, super::vswprintf);
    variadic_stub!(fwprintf, 2, super::vfwprintf);
    variadic_stub!(wprintf, 1, super::vwprintf);
    variadic_stub!(fwscanf, 2, super::vfwscanf);
    variadic_stub!(wscanf, 1, super::vwscanf);
    variadic_stub!(swscanf, 2, super::vswscanf);
    // `long double` is not distinguished by this library: `wcstold`
    // returns `wcstod`'s result converted to the `long double` format.
    crate::arch::va::long_double_stub!(wcstold, super::wcstod);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn utf8_round_trip() {
        let text = "héllo, 世界! 🎉";
        let cstr = std::ffi::CString::new(text).unwrap();
        let mut wide = [0 as WChar; 32];
        // SAFETY: valid buffers.
        unsafe {
            let n = mbstowcs(wide.as_mut_ptr(), cstr.as_ptr(), 32);
            assert_eq!(n, text.chars().count());
            let expected: Vec<WChar> = text.chars().map(|c| c as WChar).collect();
            assert_eq!(&wide[..n], &expected[..]);
            assert_eq!(mbstowcs(ptr::null_mut(), cstr.as_ptr(), 0), n);
            assert_eq!(wcslen(wide.as_ptr()), n);
            let mut back = [0u8; 64];
            let m = wcstombs(back.as_mut_ptr() as *mut c_char, wide.as_ptr(), 64);
            assert_eq!(m, text.len());
            assert_eq!(&back[..m], text.as_bytes());
            // Truncated output stops at a character boundary.
            let m = wcstombs(back.as_mut_ptr() as *mut c_char, wide.as_ptr(), 2);
            assert_eq!(m, 1);
            // Invalid input.
            assert_eq!(
                mbstowcs(wide.as_mut_ptr(), b"\xff\0".as_ptr() as *const c_char, 32),
                usize::MAX
            );
            assert_eq!(
                mbstowcs(
                    wide.as_mut_ptr(),
                    b"\xc0\x80\0".as_ptr() as *const c_char,
                    32
                ),
                usize::MAX
            );
            assert_eq!(
                mbstowcs(
                    wide.as_mut_ptr(),
                    b"\xed\xa0\x80\0".as_ptr() as *const c_char,
                    32
                ),
                usize::MAX
            );
            // Restartable decoding across a split sequence.
            let mut st = MbState::default();
            let mut wc = 0;
            let euro = "€".as_bytes();
            assert_eq!(
                mbrtowc(&mut wc, euro.as_ptr() as *const c_char, 1, &mut st),
                usize::MAX - 1
            );
            assert_eq!(mbsinit(&st), 0);
            assert_eq!(
                mbrtowc(&mut wc, euro[1..].as_ptr() as *const c_char, 2, &mut st),
                2
            );
            assert_eq!(wc, 0x20ac);
            assert_eq!(mbsinit(&st), 1);
            assert_eq!(mbrtowc(&mut wc, c"".as_ptr(), 1, ptr::null_mut()), 0);
            let mut out = [0u8; 4];
            assert_eq!(
                wcrtomb(out.as_mut_ptr() as *mut c_char, 0x1f389, ptr::null_mut()),
                4
            );
            assert_eq!(
                wcrtomb(out.as_mut_ptr() as *mut c_char, 0xd800, ptr::null_mut()),
                usize::MAX
            );
            assert_eq!(wctomb(out.as_mut_ptr() as *mut c_char, b'a' as WChar), 1);
            assert_eq!(mblen(c"\u{e9}".as_ptr(), 2), 2);
        }
        assert_eq!(btowc(b'a' as c_int), b'a' as WInt);
        assert_eq!(btowc(0x80), WEOF);
        assert_eq!(wctob(0x20ac), -1);
    }

    #[test]
    fn wide_strings_and_classes() {
        let a: Vec<WChar> = "hello".chars().map(|c| c as WChar).chain([0]).collect();
        let b: Vec<WChar> = "help".chars().map(|c| c as WChar).chain([0]).collect();
        // SAFETY: NUL-terminated wide strings.
        unsafe {
            assert!(wcscmp(a.as_ptr(), b.as_ptr()) < 0);
            assert_eq!(wcsncmp(a.as_ptr(), b.as_ptr(), 3), 0);
            assert_eq!(
                wcschr(a.as_ptr(), 'l' as WChar),
                a.as_ptr().add(2) as *mut WChar
            );
            assert_eq!(
                wcsrchr(a.as_ptr(), 'l' as WChar),
                a.as_ptr().add(3) as *mut WChar
            );
            let needle: Vec<WChar> = "ll".chars().map(|c| c as WChar).chain([0]).collect();
            assert_eq!(
                wcsstr(a.as_ptr(), needle.as_ptr()),
                a.as_ptr().add(2) as *mut WChar
            );
            assert_eq!(wcsspn(a.as_ptr(), b.as_ptr()), 4);
            let mut buf = [0 as WChar; 16];
            wcscpy(buf.as_mut_ptr(), a.as_ptr());
            wcscat(buf.as_mut_ptr(), b.as_ptr());
            assert_eq!(wcslen(buf.as_ptr()), 9);
            let d = wcsdup(a.as_ptr());
            assert_eq!(wcscmp(d, a.as_ptr()), 0);
            malloc::dealloc(d as *mut u8);
            let num: Vec<WChar> = " -42x".chars().map(|c| c as WChar).chain([0]).collect();
            let mut end = ptr::null_mut();
            assert_eq!(wcstol(num.as_ptr(), &mut end, 10), -42);
            assert_eq!(end, num.as_ptr().add(4) as *mut WChar);
            let f: Vec<WChar> = "2.5".chars().map(|c| c as WChar).chain([0]).collect();
            assert_eq!(wcstod(f.as_ptr(), ptr::null_mut()), 2.5);
            assert_eq!(wctype(c"alpha".as_ptr()), 2);
            assert_eq!(iswctype('x' as WInt, wctype(c"alpha".as_ptr())), 1);
            assert_eq!(wctype(c"nope".as_ptr()), 0);
        }
        assert_eq!(iswalpha('é' as WInt), 1);
        assert_eq!(iswalpha('世' as WInt), 1);
        assert_eq!(iswdigit('٣' as WInt), 0);
        assert_eq!(iswdigit('7' as WInt), 1);
        assert_eq!(iswspace(' ' as WInt), 1);
        assert_eq!(iswupper('Ä' as WInt), 1);
        assert_eq!(towupper('é' as WInt), 'É' as WInt);
        assert_eq!(towlower('Σ' as WInt), 'σ' as WInt);
        assert_eq!(
            towupper('ß' as WInt),
            'ß' as WInt,
            "no single-char uppercase"
        );
        assert_eq!(iswalpha(WEOF), 0);
        assert_eq!(wcwidth('a' as WChar), 1);
        assert_eq!(wcwidth('世' as WChar), 2);
        assert_eq!(wcwidth(0x301), 0);
        assert_eq!(wcwidth(7), -1);
    }
}
