//! glibc-compatibility symbols.
//!
//! Prebuilt static libraries compiled against glibc's headers reference a
//! few glibc-only symbols: the `_FORTIFY_SOURCE` `__*_chk` entry points,
//! the `__isoc99_`/`__isoc23_` aliases, `__libc_single_threaded`,
//! `_dl_find_object` (used by libgcc's unwinder), `gettext` and
//! `arc4random`. Providing them lets, for example, the distribution's
//! `libstdc++.a` link against this library. The checked functions abort
//! on overflow, like glibc's.

use crate::c_char;
use crate::errno::Errno;
use crate::string::search;
use crate::sys;
use crate::thread::tls::Elf64Phdr;
use core::ffi::{c_int, c_long, c_uint, c_void};
use core::ptr;

/// glibc's hint that a program has never created a thread. Cleared when
/// the first thread is created.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub static mut __libc_single_threaded: u8 = 1;

/// Reports a fortify check failure and aborts.
#[cold]
fn chk_fail() -> ! {
    sys::write_all(2, b"*** buffer overflow detected ***: terminated\n").ok();
    crate::exit::abort_now()
}

// ---------------------------------------------------------------------
// _FORTIFY_SOURCE

/// `__memcpy_chk`.
///
/// # Safety
/// As for `memcpy`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __memcpy_chk(
    dst: *mut c_void,
    src: *const c_void,
    n: usize,
    dstlen: usize,
) -> *mut c_void {
    if n > dstlen {
        chk_fail();
    }
    // SAFETY: forwarded.
    unsafe { crate::string::mem::memcpy(dst, src, n) }
}

/// `__memmove_chk`.
///
/// # Safety
/// As for `memmove`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __memmove_chk(
    dst: *mut c_void,
    src: *const c_void,
    n: usize,
    dstlen: usize,
) -> *mut c_void {
    if n > dstlen {
        chk_fail();
    }
    // SAFETY: forwarded.
    unsafe { crate::string::mem::memmove(dst, src, n) }
}

/// `__memset_chk`.
///
/// # Safety
/// As for `memset`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __memset_chk(
    dst: *mut c_void,
    c: c_int,
    n: usize,
    dstlen: usize,
) -> *mut c_void {
    if n > dstlen {
        chk_fail();
    }
    // SAFETY: forwarded.
    unsafe { crate::string::mem::memset(dst, c, n) }
}

/// `__strcpy_chk`.
///
/// # Safety
/// As for `strcpy`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __strcpy_chk(
    dst: *mut c_char,
    src: *const c_char,
    dstlen: usize,
) -> *mut c_char {
    // SAFETY: caller contract.
    if unsafe { search::strlen(src as *const u8) } >= dstlen {
        chk_fail();
    }
    // SAFETY: forwarded.
    unsafe { crate::string::str::strcpy(dst, src) }
}

/// `__stpcpy_chk`.
///
/// # Safety
/// As for `stpcpy`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __stpcpy_chk(
    dst: *mut c_char,
    src: *const c_char,
    dstlen: usize,
) -> *mut c_char {
    // SAFETY: caller contract.
    if unsafe { search::strlen(src as *const u8) } >= dstlen {
        chk_fail();
    }
    // SAFETY: forwarded.
    unsafe { crate::string::str::stpcpy(dst, src) }
}

/// `__strncpy_chk`.
///
/// # Safety
/// As for `strncpy`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __strncpy_chk(
    dst: *mut c_char,
    src: *const c_char,
    n: usize,
    dstlen: usize,
) -> *mut c_char {
    if n > dstlen {
        chk_fail();
    }
    // SAFETY: forwarded.
    unsafe { crate::string::str::strncpy(dst, src, n) }
}

/// `__strcat_chk`.
///
/// # Safety
/// As for `strcat`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __strcat_chk(
    dst: *mut c_char,
    src: *const c_char,
    dstlen: usize,
) -> *mut c_char {
    // SAFETY: caller contract.
    let (dl, sl) = unsafe {
        (
            search::strlen(dst as *const u8),
            search::strlen(src as *const u8),
        )
    };
    if dl.saturating_add(sl).saturating_add(1) > dstlen {
        chk_fail();
    }
    // SAFETY: forwarded.
    unsafe { crate::string::str::strcat(dst, src) }
}

/// `__strncat_chk`.
///
/// # Safety
/// As for `strncat`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __strncat_chk(
    dst: *mut c_char,
    src: *const c_char,
    n: usize,
    dstlen: usize,
) -> *mut c_char {
    // SAFETY: caller contract.
    let (dl, sl) = unsafe {
        (
            search::strlen(dst as *const u8),
            search::strnlen(src as *const u8, n),
        )
    };
    if dl.saturating_add(sl).saturating_add(1) > dstlen {
        chk_fail();
    }
    // SAFETY: forwarded.
    unsafe { crate::string::str::strncat(dst, src, n) }
}

/// `__read_chk`.
///
/// # Safety
/// As for `read`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __read_chk(fd: c_int, buf: *mut c_void, n: usize, buflen: usize) -> isize {
    if n > buflen {
        chk_fail();
    }
    // SAFETY: forwarded.
    unsafe { crate::unistd::read(fd, buf, n) }
}

/// `__fgets_chk`.
///
/// # Safety
/// As for `fgets`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __fgets_chk(
    s: *mut c_char,
    size: usize,
    n: c_int,
    f: *mut crate::stdio::File,
) -> *mut c_char {
    if n < 0 || n as usize > size {
        chk_fail();
    }
    // SAFETY: forwarded.
    unsafe { crate::stdio::fgets(s, n, f) }
}

/// `__vsprintf_chk`: `vsprintf` that aborts if the output would exceed
/// `slen` bytes (`SIZE_MAX` when unknown).
///
/// # Safety
/// As for `vsprintf`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __vsprintf_chk(
    s: *mut c_char,
    _flag: c_int,
    slen: usize,
    fmt: *const c_char,
    ap: *mut crate::arch::va::VaList,
) -> c_int {
    // SAFETY: forwarded.
    let r = unsafe { crate::stdio::printf::vsnprintf(s, slen, fmt, ap) };
    if r >= 0 && r as usize >= slen {
        chk_fail();
    }
    r
}

/// `__vsnprintf_chk`.
///
/// # Safety
/// As for `vsnprintf`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __vsnprintf_chk(
    s: *mut c_char,
    maxlen: usize,
    _flag: c_int,
    slen: usize,
    fmt: *const c_char,
    ap: *mut crate::arch::va::VaList,
) -> c_int {
    if maxlen > slen {
        chk_fail();
    }
    // SAFETY: forwarded.
    unsafe { crate::stdio::printf::vsnprintf(s, maxlen, fmt, ap) }
}

/// `__vprintf_chk`.
///
/// # Safety
/// As for `vprintf`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __vprintf_chk(
    _flag: c_int,
    fmt: *const c_char,
    ap: *mut crate::arch::va::VaList,
) -> c_int {
    // SAFETY: forwarded.
    unsafe { crate::stdio::printf::vprintf(fmt, ap) }
}

/// `__vfprintf_chk`.
///
/// # Safety
/// As for `vfprintf`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __vfprintf_chk(
    f: *mut crate::stdio::File,
    _flag: c_int,
    fmt: *const c_char,
    ap: *mut crate::arch::va::VaList,
) -> c_int {
    // SAFETY: forwarded.
    unsafe { crate::stdio::printf::vfprintf(f, fmt, ap) }
}

// ---------------------------------------------------------------------
// __isoc99_ / __isoc23_ aliases (glibc renames these for C99/C23 semantics,
// which are the only ones this library implements).

macro_rules! alias {
    ($($(#[$m:meta])* $alias:ident => $target:path, ($($arg:ident: $ty:ty),*) -> $ret:ty;)*) => {
        $(
            $(#[$m])*
            #[allow(unused_unsafe)]
            #[cfg_attr(not(test), unsafe(no_mangle))]
            pub unsafe extern "C" fn $alias($($arg: $ty),*) -> $ret {
                // SAFETY: forwarded.
                unsafe { $target($($arg),*) }
            }
        )*
    };
}

alias! {
    /// `__isoc23_strtol`.
    ///
    /// # Safety
    /// As for `strtol`.
    __isoc23_strtol => crate::stdlib::num::strtol, (s: *const c_char, end: *mut *mut c_char, base: c_int) -> c_long;
    /// `__isoc23_strtoul`.
    ///
    /// # Safety
    /// As for `strtoul`.
    __isoc23_strtoul => crate::stdlib::num::strtoul, (s: *const c_char, end: *mut *mut c_char, base: c_int) -> core::ffi::c_ulong;
    /// `__isoc23_strtoll`.
    ///
    /// # Safety
    /// As for `strtoll`.
    __isoc23_strtoll => crate::stdlib::num::strtoll, (s: *const c_char, end: *mut *mut c_char, base: c_int) -> core::ffi::c_longlong;
    /// `__isoc23_strtoull`.
    ///
    /// # Safety
    /// As for `strtoull`.
    __isoc23_strtoull => crate::stdlib::num::strtoull, (s: *const c_char, end: *mut *mut c_char, base: c_int) -> core::ffi::c_ulonglong;
    /// `__isoc99_vsscanf`.
    ///
    /// # Safety
    /// As for `vsscanf`.
    __isoc99_vsscanf => crate::stdio::scanf::vsscanf, (s: *const c_char, fmt: *const c_char, ap: *mut crate::arch::va::VaList) -> c_int;
    /// `__isoc99_vfscanf`.
    ///
    /// # Safety
    /// As for `vfscanf`.
    __isoc99_vfscanf => crate::stdio::scanf::vfscanf, (f: *mut crate::stdio::File, fmt: *const c_char, ap: *mut crate::arch::va::VaList) -> c_int;
    /// `__isoc99_vscanf`.
    ///
    /// # Safety
    /// As for `vscanf`.
    __isoc99_vscanf => crate::stdio::scanf::vscanf, (fmt: *const c_char, ap: *mut crate::arch::va::VaList) -> c_int;
    /// `__isoc23_vsscanf`.
    ///
    /// # Safety
    /// As for `vsscanf`.
    __isoc23_vsscanf => crate::stdio::scanf::vsscanf, (s: *const c_char, fmt: *const c_char, ap: *mut crate::arch::va::VaList) -> c_int;
    /// `__isoc23_vfscanf`.
    ///
    /// # Safety
    /// As for `vfscanf`.
    __isoc23_vfscanf => crate::stdio::scanf::vfscanf, (f: *mut crate::stdio::File, fmt: *const c_char, ap: *mut crate::arch::va::VaList) -> c_int;
    /// `__isoc23_vscanf`.
    ///
    /// # Safety
    /// As for `vscanf`.
    __isoc23_vscanf => crate::stdio::scanf::vscanf, (fmt: *const c_char, ap: *mut crate::arch::va::VaList) -> c_int;
}

type File = crate::stdio::File;
type Locale = *mut c_void;
type WChar = crate::wchar::WChar;
type WInt = crate::wchar::WInt;

alias! {
    /// `fopen64`: `off_t` is always 64 bits here.
    ///
    /// # Safety
    /// As for `fopen`.
    fopen64 => crate::stdio::fopen, (path: *const c_char, mode: *const c_char) -> *mut File;
    /// `fseeko64`.
    ///
    /// # Safety
    /// As for `fseeko`.
    fseeko64 => crate::stdio::fseeko, (f: *mut File, off: i64, whence: c_int) -> c_int;
    /// `ftello64`.
    ///
    /// # Safety
    /// As for `ftello`.
    ftello64 => crate::stdio::ftello, (f: *mut File) -> i64;
    /// `lseek64`.
    ///
    /// # Safety
    /// None.
    lseek64 => crate::unistd::lseek, (fd: c_int, off: i64, whence: c_int) -> i64;
    /// `fstat64`.
    ///
    /// # Safety
    /// As for `fstat`.
    fstat64 => crate::fs::fstat, (fd: c_int, st: *mut crate::fs::Stat) -> c_int;
}

// glibc-internal locale entry points, all with a trailing (ignored)
// locale argument: this library only has the C locale.

/// `__nl_langinfo_l`.
///
/// # Safety
/// None.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __nl_langinfo_l(item: c_int, _loc: Locale) -> *mut c_char {
    crate::locale::nl_langinfo(item)
}

alias! {
    /// `__uselocale`.
    ///
    /// # Safety
    /// As for `uselocale`.
    __uselocale => crate::locale::uselocale, (l: Locale) -> Locale;
    /// `__newlocale`.
    ///
    /// # Safety
    /// As for `newlocale`.
    __newlocale => crate::locale::newlocale, (mask: c_int, name: *const c_char, base: Locale) -> Locale;
    /// `__duplocale`.
    ///
    /// # Safety
    /// As for `duplocale`.
    __duplocale => crate::locale::duplocale, (l: Locale) -> Locale;
    /// `__freelocale`.
    ///
    /// # Safety
    /// As for `freelocale`.
    __freelocale => crate::locale::freelocale, (l: Locale) -> ();
}

macro_rules! with_locale {
    ($($(#[$m:meta])* $alias:ident => $target:path, ($($arg:ident: $ty:ty),*) -> $ret:ty;)*) => {
        $(
            $(#[$m])*
            #[allow(unused_unsafe)]
            #[cfg_attr(not(test), unsafe(no_mangle))]
            pub unsafe extern "C" fn $alias($($arg: $ty,)* _loc: Locale) -> $ret {
                // SAFETY: forwarded.
                unsafe { $target($($arg),*) }
            }
        )*
    };
}

with_locale! {
    /// `__wctype_l`.
    ///
    /// # Safety
    /// As for `wctype`.
    __wctype_l => crate::wchar::wctype, (name: *const c_char) -> core::ffi::c_ulong;
    /// `__iswctype_l`.
    ///
    /// # Safety
    /// None.
    __iswctype_l => crate::wchar::iswctype, (c: WInt, class: core::ffi::c_ulong) -> c_int;
    /// `__towupper_l`.
    ///
    /// # Safety
    /// None.
    __towupper_l => crate::wchar::towupper, (c: WInt) -> WInt;
    /// `__towlower_l`.
    ///
    /// # Safety
    /// None.
    __towlower_l => crate::wchar::towlower, (c: WInt) -> WInt;
    /// `__wcscoll_l`.
    ///
    /// # Safety
    /// As for `wcscoll`.
    __wcscoll_l => crate::wchar::wcscoll, (a: *const WChar, b: *const WChar) -> c_int;
    /// `__wcsxfrm_l`.
    ///
    /// # Safety
    /// As for `wcsxfrm`.
    __wcsxfrm_l => crate::wchar::wcsxfrm, (dst: *mut WChar, src: *const WChar, n: usize) -> usize;
    /// `__strcoll_l`.
    ///
    /// # Safety
    /// As for `strcoll`.
    __strcoll_l => crate::string::str::strcoll, (a: *const c_char, b: *const c_char) -> c_int;
    /// `__strxfrm_l`.
    ///
    /// # Safety
    /// As for `strxfrm`.
    __strxfrm_l => crate::string::str::strxfrm, (dst: *mut c_char, src: *const c_char, n: usize) -> usize;
    /// `__strtof_l`.
    ///
    /// # Safety
    /// As for `strtof`.
    __strtof_l => crate::stdlib::num::strtof, (s: *const c_char, end: *mut *mut c_char) -> f32;
    /// `__strtod_l`.
    ///
    /// # Safety
    /// As for `strtod`.
    __strtod_l => crate::stdlib::num::strtod, (s: *const c_char, end: *mut *mut c_char) -> f64;
    /// `__strftime_l`.
    ///
    /// # Safety
    /// As for `strftime`.
    __strftime_l => crate::time::strftime::strftime, (s: *mut c_char, max: usize, fmt: *const c_char, tm: *const crate::time::Tm) -> usize;
    /// `__wcsftime_l`.
    ///
    /// # Safety
    /// As for `wcsftime`.
    __wcsftime_l => crate::wchar::wcsftime, (s: *mut WChar, max: usize, fmt: *const WChar, tm: *const crate::time::Tm) -> usize;
}

/// `__ctype_get_mb_cur_max`: UTF-8.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn __ctype_get_mb_cur_max() -> usize {
    4
}

/// `get_nprocs(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn get_nprocs() -> c_int {
    crate::fs::sysconf(84).max(1) as c_int
}

/// `get_nprocs_conf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn get_nprocs_conf() -> c_int {
    get_nprocs()
}

/// `bind_textdomain_codeset(3)`: no catalogs.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn bind_textdomain_codeset(
    _domain: *const c_char,
    _codeset: *const c_char,
) -> *mut c_char {
    ptr::null_mut()
}

/// `__mbsrtowcs_chk`.
///
/// # Safety
/// As for `mbsrtowcs`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __mbsrtowcs_chk(
    dst: *mut WChar,
    src: *mut *const c_char,
    len: usize,
    ps: *mut crate::wchar::MbState,
    dstlen: usize,
) -> usize {
    if len > dstlen {
        chk_fail();
    }
    // SAFETY: forwarded.
    unsafe { crate::wchar::mbsrtowcs(dst, src, len, ps) }
}

/// `__mbsnrtowcs_chk`.
///
/// # Safety
/// As for `mbsnrtowcs`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __mbsnrtowcs_chk(
    dst: *mut WChar,
    src: *mut *const c_char,
    nms: usize,
    len: usize,
    ps: *mut crate::wchar::MbState,
    dstlen: usize,
) -> usize {
    if len > dstlen {
        chk_fail();
    }
    // SAFETY: forwarded.
    unsafe { crate::wchar::mbsnrtowcs(dst, src, nms, len, ps) }
}

/// `__wmemcpy_chk`.
///
/// # Safety
/// As for `wmemcpy`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __wmemcpy_chk(
    dst: *mut WChar,
    src: *const WChar,
    n: usize,
    dstlen: usize,
) -> *mut WChar {
    if n > dstlen {
        chk_fail();
    }
    // SAFETY: forwarded.
    unsafe { crate::wchar::wmemcpy(dst, src, n) }
}

/// `__wmemset_chk`.
///
/// # Safety
/// As for `wmemset`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __wmemset_chk(
    dst: *mut WChar,
    c: WChar,
    n: usize,
    dstlen: usize,
) -> *mut WChar {
    if n > dstlen {
        chk_fail();
    }
    // SAFETY: forwarded.
    unsafe { crate::wchar::wmemset(dst, c, n) }
}

#[cfg(not(test))]
mod stubs {
    use crate::arch::va::variadic_stub;
    // `long double` results go in `st(0)`: convert `strtod`'s `double`.
    core::arch::global_asm!(
        ".globl strtold_l",
        ".type strtold_l, @function",
        "strtold_l:",
        ".globl __strtold_l",
        ".type __strtold_l, @function",
        "__strtold_l:",
        "sub rsp, 8",
        "call {strtod}",
        "movsd qword ptr [rsp], xmm0",
        "fld qword ptr [rsp]",
        "add rsp, 8",
        "ret",
        strtod = sym crate::stdlib::num::strtod,
    );
    variadic_stub!(__sprintf_chk, 4, "r8", super::__vsprintf_chk);
    variadic_stub!(__snprintf_chk, 5, "r9", super::__vsnprintf_chk);
    variadic_stub!(__printf_chk, 2, "rdx", super::__vprintf_chk);
    variadic_stub!(__fprintf_chk, 3, "rcx", super::__vfprintf_chk);
    variadic_stub!(__isoc99_sscanf, 2, "rdx", crate::stdio::scanf::vsscanf);
    variadic_stub!(__isoc99_fscanf, 2, "rdx", crate::stdio::scanf::vfscanf);
    variadic_stub!(__isoc99_scanf, 1, "rsi", crate::stdio::scanf::vscanf);
    variadic_stub!(__isoc23_sscanf, 2, "rdx", crate::stdio::scanf::vsscanf);
    variadic_stub!(__isoc23_fscanf, 2, "rdx", crate::stdio::scanf::vfscanf);
    variadic_stub!(__isoc23_scanf, 1, "rsi", crate::stdio::scanf::vscanf);
}

// ---------------------------------------------------------------------
// gettext, arc4random

/// `gettext(3)`: no message catalogs, the message is its own translation.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn gettext(msg: *const c_char) -> *mut c_char {
    msg as *mut c_char
}

/// `dgettext(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn dgettext(_domain: *const c_char, msg: *const c_char) -> *mut c_char {
    msg as *mut c_char
}

/// `dcgettext(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn dcgettext(
    _domain: *const c_char,
    msg: *const c_char,
    _category: c_int,
) -> *mut c_char {
    msg as *mut c_char
}

/// `textdomain(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn textdomain(domain: *const c_char) -> *mut c_char {
    domain as *mut c_char
}

/// `bindtextdomain(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn bindtextdomain(_domain: *const c_char, dir: *const c_char) -> *mut c_char {
    dir as *mut c_char
}

/// `arc4random_buf(3)`: kernel randomness (it never fails).
///
/// # Safety
/// `buf` must be valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn arc4random_buf(buf: *mut c_void, n: usize) {
    let mut done = 0;
    while done < n {
        // SAFETY: caller contract.
        match unsafe {
            crate::fs::getrandom(buf.cast::<u8>().add(done) as *mut c_void, n - done, 0)
        } {
            r if r > 0 => done += r as usize,
            _ => {
                if Errno::get() != Errno::EINTR {
                    crate::exit::abort_now();
                }
            }
        }
    }
}

/// `arc4random(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn arc4random() -> u32 {
    let mut v = 0u32;
    // SAFETY: valid buffer.
    unsafe { arc4random_buf(&mut v as *mut u32 as *mut c_void, 4) };
    v
}

/// `arc4random_uniform(3)`: unbiased by rejection.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn arc4random_uniform(bound: u32) -> u32 {
    if bound < 2 {
        return 0;
    }
    let min = bound.wrapping_neg() % bound;
    loop {
        let r = arc4random();
        if r >= min {
            return r % bound;
        }
    }
}

// ---------------------------------------------------------------------
// _dl_find_object

/// glibc's `struct dl_find_object`.
#[repr(C)]
pub struct DlFindObject {
    flags: u64,
    map_start: *mut c_void,
    map_end: *mut c_void,
    link_map: *mut c_void,
    eh_frame: *mut c_void,
    reserved: [u64; 7],
}

const PT_LOAD: u32 = 1;
const PT_PHDR: u32 = 6;
const PT_GNU_EH_FRAME: u32 = 0x6474_e550;

/// `_dl_find_object`: describes the (only) object containing `addr`, for
/// libgcc's unwinder. Returns 0 on success, -1 if the address is outside
/// the executable.
///
/// # Safety
/// `result` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn _dl_find_object(addr: *mut c_void, result: *mut DlFindObject) -> c_int {
    let phdr = crate::start::auxval(crate::start::auxv::AT_PHDR).unwrap_or(0) as *const Elf64Phdr;
    let phnum = crate::start::auxval(crate::start::auxv::AT_PHNUM).unwrap_or(0);
    if phdr.is_null() {
        return -1;
    }
    // SAFETY: AT_PHDR/AT_PHNUM describe the executable's own headers.
    let headers = unsafe { core::slice::from_raw_parts(phdr, phnum) };
    // Load bias: zero for a non-PIE executable; otherwise the PT_PHDR
    // entry reveals it (as in `dl_iterate_phdr`).
    let mut base = 0usize;
    for ph in headers {
        if ph.p_type == PT_PHDR {
            base = (phdr as usize).wrapping_sub(ph.p_vaddr as usize);
        }
    }
    let (mut lo, mut hi, mut found, mut eh) = (usize::MAX, 0usize, false, ptr::null_mut());
    for ph in headers {
        let start = base.wrapping_add(ph.p_vaddr as usize);
        let end = start.wrapping_add(ph.p_memsz as usize);
        match ph.p_type {
            PT_LOAD => {
                lo = lo.min(start);
                hi = hi.max(end);
                if (start..end).contains(&(addr as usize)) {
                    found = true;
                }
            }
            PT_GNU_EH_FRAME => eh = start as *mut c_void,
            _ => {}
        }
    }
    if !found {
        return -1;
    }
    // SAFETY: caller contract.
    unsafe {
        result.write(DlFindObject {
            flags: 0,
            map_start: lo as *mut c_void,
            map_end: hi as *mut c_void,
            link_map: ptr::null_mut(),
            eh_frame: eh,
            reserved: [0; 7],
        });
    }
    0
}

/// Type of the `flag` arguments above, kept for documentation.
#[allow(dead_code)]
type Flag = c_uint;

// ---------------------------------------------------------------------
// glibc's ctype tables (`__ctype_b_loc` and friends), used by code
// compiled against glibc's <ctype.h> macros and by libstdc++'s
// `ctype<char>`.

const IS_UPPER: u16 = 0x100;
const IS_LOWER: u16 = 0x200;
const IS_ALPHA: u16 = 0x400;
const IS_DIGIT: u16 = 0x800;
const IS_XDIGIT: u16 = 0x1000;
const IS_SPACE: u16 = 0x2000;
const IS_PRINT: u16 = 0x4000;
const IS_GRAPH: u16 = 0x8000;
const IS_BLANK: u16 = 0x1;
const IS_CNTRL: u16 = 0x2;
const IS_PUNCT: u16 = 0x4;
const IS_ALNUM: u16 = 0x8;

/// Class bits of byte `b` in the C locale, glibc's layout.
const fn class_bits(b: u8) -> u16 {
    let mut m = 0;
    if b.is_ascii_uppercase() {
        m |= IS_UPPER | IS_ALPHA | IS_ALNUM;
    }
    if b.is_ascii_lowercase() {
        m |= IS_LOWER | IS_ALPHA | IS_ALNUM;
    }
    if b.is_ascii_digit() {
        m |= IS_DIGIT | IS_ALNUM;
    }
    if b.is_ascii_hexdigit() {
        m |= IS_XDIGIT;
    }
    if matches!(b, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r') {
        m |= IS_SPACE;
    }
    if b == b' ' || b == b'\t' {
        m |= IS_BLANK;
    }
    if b < 0x20 || b == 0x7f {
        m |= IS_CNTRL;
    }
    if b.is_ascii_punctuation() {
        m |= IS_PUNCT;
    }
    if b.is_ascii_graphic() {
        m |= IS_GRAPH | IS_PRINT;
    }
    if b == b' ' {
        m |= IS_PRINT;
    }
    m
}

/// 384 entries: indices `-128..=255` (bytes above 127 and negative `char`
/// values classify as nothing).
struct CtypeTables {
    class: [u16; 384],
    lower: [i32; 384],
    upper: [i32; 384],
}

const fn build_ctype_tables() -> CtypeTables {
    let mut t = CtypeTables {
        class: [0; 384],
        lower: [0; 384],
        upper: [0; 384],
    };
    let mut i = 0;
    while i < 384 {
        let c = i as i32 - 128;
        if c >= 0 && c < 128 {
            let b = c as u8;
            t.class[i] = class_bits(b);
            t.lower[i] = b.to_ascii_lowercase() as i32;
            t.upper[i] = b.to_ascii_uppercase() as i32;
        } else {
            t.lower[i] = c;
            t.upper[i] = c;
        }
        i += 1;
    }
    t
}

static CTYPE: CtypeTables = build_ctype_tables();
static CTYPE_B: &u16 = &CTYPE.class[128];
static CTYPE_TOLOWER: &i32 = &CTYPE.lower[128];
static CTYPE_TOUPPER: &i32 = &CTYPE.upper[128];

/// glibc's `struct __locale_struct`, which libstdc++ (built for glibc)
/// dereferences to find the ctype tables of a `locale_t`. The one C
/// locale object this library hands out uses this layout.
#[repr(C)]
pub struct LocaleStruct {
    locales: [*const c_void; 13],
    ctype_b: &'static u16,
    ctype_tolower: &'static i32,
    ctype_toupper: &'static i32,
    names: [*const c_char; 13],
}

// SAFETY: immutable after construction.
unsafe impl Sync for LocaleStruct {}

/// The C locale.
pub static C_LOCALE: LocaleStruct = LocaleStruct {
    locales: [ptr::null(); 13],
    ctype_b: &CTYPE.class[128],
    ctype_tolower: &CTYPE.lower[128],
    ctype_toupper: &CTYPE.upper[128],
    names: [c"C".as_ptr(); 13],
};

/// `__ctype_b_loc`: pointer to the class table, offset so that indices
/// `-128..=255` are valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn __ctype_b_loc() -> *const *const u16 {
    &raw const CTYPE_B as *const *const u16
}

/// `__ctype_tolower_loc`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn __ctype_tolower_loc() -> *const *const i32 {
    &raw const CTYPE_TOLOWER as *const *const i32
}

/// `__ctype_toupper_loc`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn __ctype_toupper_loc() -> *const *const i32 {
    &raw const CTYPE_TOUPPER as *const *const i32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ctype_tables_match_ctype() {
        use crate::string::ctype;
        // SAFETY: the tables are valid for indices -128..=255.
        unsafe {
            let b = *__ctype_b_loc();
            let lo = *__ctype_tolower_loc();
            let up = *__ctype_toupper_loc();
            for c in -128i32..256 {
                let m = *b.offset(c as isize);
                assert_eq!(m & IS_ALPHA != 0, ctype::isalpha(c) != 0, "{c}");
                assert_eq!(m & IS_DIGIT != 0, ctype::isdigit(c) != 0, "{c}");
                assert_eq!(m & IS_SPACE != 0, ctype::isspace(c) != 0, "{c}");
                assert_eq!(m & IS_PUNCT != 0, ctype::ispunct(c) != 0, "{c}");
                assert_eq!(m & IS_PRINT != 0, ctype::isprint(c) != 0, "{c}");
                assert_eq!(m & IS_CNTRL != 0, ctype::iscntrl(c) != 0, "{c}");
                assert_eq!(*lo.offset(c as isize), ctype::tolower(c), "{c}");
                assert_eq!(*up.offset(c as isize), ctype::toupper(c), "{c}");
            }
        }
    }

    #[test]
    fn arc4random_uniform_in_range() {
        for _ in 0..1000 {
            assert!(arc4random_uniform(7) < 7);
        }
        assert_eq!(arc4random_uniform(1), 0);
    }
}
