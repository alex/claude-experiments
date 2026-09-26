//! The `str*` family.
//!
//! The search and compare functions dispatch to the SIMD kernels in
//! [`super::search`]; the copying functions are built from `strlen` and
//! `memcpy`, which is both simple and fast (two passes over data that is
//! in cache anyway).

use super::mem::{memcpy, memmove};
use super::search;
use crate::c_char;
use core::ffi::{c_int, c_void};
use core::{ptr, slice};

/// `strlen(3)`.
///
/// # Safety
/// `s` must point to a NUL-terminated string.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strlen(s: *const c_char) -> usize {
    // SAFETY: forwarded from the caller.
    unsafe { search::strlen(s as *const u8) }
}

/// `strnlen(3)`.
///
/// # Safety
/// `s` must be readable up to its NUL terminator or `max` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strnlen(s: *const c_char, max: usize) -> usize {
    // SAFETY: forwarded from the caller.
    unsafe { search::strnlen(s as *const u8, max) }
}

/// `strcmp(3)`.
///
/// # Safety
/// Both must be NUL-terminated strings.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strcmp(a: *const c_char, b: *const c_char) -> c_int {
    // SAFETY: forwarded from the caller.
    unsafe { search::strcmp(a as *const u8, b as *const u8) }
}

/// `strncmp(3)`.
///
/// # Safety
/// Both must be NUL-terminated strings or readable for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strncmp(a: *const c_char, b: *const c_char, n: usize) -> c_int {
    // SAFETY: forwarded from the caller.
    unsafe { search::strncmp(a as *const u8, b as *const u8, n) }
}

/// `strcoll(3)`: in the C locale this is `strcmp`.
///
/// # Safety
/// Both must be NUL-terminated strings.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strcoll(a: *const c_char, b: *const c_char) -> c_int {
    // SAFETY: forwarded from the caller.
    unsafe { strcmp(a, b) }
}

/// `strxfrm(3)`: in the C locale this is a bounded copy.
///
/// # Safety
/// `src` must be NUL-terminated; `dst` must be valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strxfrm(dst: *mut c_char, src: *const c_char, n: usize) -> usize {
    // SAFETY: forwarded from the caller.
    unsafe {
        let len = strlen(src);
        if n > len {
            memcpy(dst as *mut c_void, src as *const c_void, len + 1);
        }
        len
    }
}

/// `strcpy(3)`.
///
/// # Safety
/// `src` must be NUL-terminated and `dst` large enough to hold it.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strcpy(dst: *mut c_char, src: *const c_char) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe {
        memcpy(dst as *mut c_void, src as *const c_void, strlen(src) + 1);
    }
    dst
}

/// `stpcpy(3)`: like `strcpy` but returns a pointer to the terminator.
///
/// # Safety
/// As for [`strcpy`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn stpcpy(dst: *mut c_char, src: *const c_char) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe {
        let len = strlen(src);
        memcpy(dst as *mut c_void, src as *const c_void, len + 1);
        dst.add(len)
    }
}

/// `strncpy(3)`: copies at most `n` bytes and pads with NULs. Note that
/// the result is not NUL-terminated if `src` is `n` bytes or longer.
///
/// # Safety
/// `dst` must be valid for `n` bytes; `src` must be NUL-terminated or
/// readable for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strncpy(dst: *mut c_char, src: *const c_char, n: usize) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe {
        stpncpy(dst, src, n);
    }
    dst
}

/// `stpncpy(3)`: as [`strncpy`], returning a pointer to the first NUL
/// written (or `dst + n`).
///
/// # Safety
/// As for [`strncpy`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn stpncpy(dst: *mut c_char, src: *const c_char, n: usize) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe {
        let len = strnlen(src, n);
        memcpy(dst as *mut c_void, src as *const c_void, len);
        ptr::write_bytes(dst.add(len), 0, n - len);
        dst.add(len)
    }
}

/// `strcat(3)`.
///
/// # Safety
/// Both must be NUL-terminated and `dst` large enough for the result.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strcat(dst: *mut c_char, src: *const c_char) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe {
        strcpy(dst.add(strlen(dst)), src);
    }
    dst
}

/// `strncat(3)`: appends at most `n` bytes of `src` and always terminates.
///
/// # Safety
/// `dst` must be NUL-terminated and large enough; `src` must be
/// NUL-terminated or readable for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strncat(dst: *mut c_char, src: *const c_char, n: usize) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe {
        let dlen = strlen(dst);
        let slen = strnlen(src, n);
        memcpy(dst.add(dlen) as *mut c_void, src as *const c_void, slen);
        *dst.add(dlen + slen) = 0;
    }
    dst
}

/// `strlcpy(3)`: bounded copy that always terminates; returns `strlen(src)`.
///
/// # Safety
/// `src` must be NUL-terminated; `dst` must be valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strlcpy(dst: *mut c_char, src: *const c_char, n: usize) -> usize {
    // SAFETY: forwarded from the caller.
    unsafe {
        let len = strlen(src);
        if n > 0 {
            let copy = len.min(n - 1);
            memcpy(dst as *mut c_void, src as *const c_void, copy);
            *dst.add(copy) = 0;
        }
        len
    }
}

/// `strlcat(3)`: bounded append that always terminates; returns the
/// length it tried to create.
///
/// # Safety
/// `src` must be NUL-terminated; `dst` must be valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strlcat(dst: *mut c_char, src: *const c_char, n: usize) -> usize {
    // SAFETY: forwarded from the caller.
    unsafe {
        let dlen = strnlen(dst, n);
        let slen = strlen(src);
        if dlen == n {
            return n + slen;
        }
        strlcpy(dst.add(dlen), src, n - dlen);
        dlen + slen
    }
}

/// `strchr(3)`. Searching for NUL returns a pointer to the terminator.
///
/// # Safety
/// `s` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strchr(s: *const c_char, c: c_int) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe { search::strchr_ptr(s as *const u8, c as u8) as *mut c_char }
}

/// `strchrnul(3)`: like `strchr` but returns the terminator when not found.
///
/// # Safety
/// `s` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strchrnul(s: *const c_char, c: c_int) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe { s.add(search::strchrnul(s as *const u8, c as u8)) as *mut c_char }
}

/// `strrchr(3)`.
///
/// # Safety
/// `s` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strrchr(s: *const c_char, c: c_int) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe {
        let len = strlen(s);
        if c as u8 == 0 {
            return s.add(len) as *mut c_char;
        }
        match search::memrchr(slice::from_raw_parts(s as *const u8, len), c as u8) {
            Some(i) => s.add(i) as *mut c_char,
            None => ptr::null_mut(),
        }
    }
}

/// `strstr(3)`.
///
/// # Safety
/// Both must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strstr(hay: *const c_char, needle: *const c_char) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe {
        let nlen = strlen(needle);
        if nlen == 0 {
            return hay as *mut c_char;
        }
        let hlen = strlen(hay);
        let h = slice::from_raw_parts(hay as *const u8, hlen);
        let n = slice::from_raw_parts(needle as *const u8, nlen);
        match search::memmem(h, n) {
            Some(i) => hay.add(i) as *mut c_char,
            None => ptr::null_mut(),
        }
    }
}

/// A 256-bit set of byte values.
struct ByteSet([u64; 4]);

impl ByteSet {
    /// Builds the set of bytes in the NUL-terminated string `s`.
    ///
    /// # Safety
    /// `s` must be NUL-terminated.
    unsafe fn from_cstr(s: *const c_char) -> Self {
        let mut set = [0u64; 4];
        // SAFETY: forwarded from the caller.
        let bytes = unsafe { slice::from_raw_parts(s as *const u8, strlen(s)) };
        for &b in bytes {
            set[(b >> 6) as usize] |= 1 << (b & 63);
        }
        ByteSet(set)
    }

    #[inline]
    fn contains(&self, b: u8) -> bool {
        self.0[(b >> 6) as usize] & (1 << (b & 63)) != 0
    }
}

/// `strspn(3)`: length of the initial segment of `s` consisting of bytes
/// from `accept`.
///
/// # Safety
/// Both must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strspn(s: *const c_char, accept: *const c_char) -> usize {
    // SAFETY: forwarded from the caller.
    unsafe {
        let set = ByteSet::from_cstr(accept);
        let mut i = 0;
        while *s.add(i) != 0 && set.contains(*s.add(i) as u8) {
            i += 1;
        }
        i
    }
}

/// `strcspn(3)`: length of the initial segment of `s` with no byte from
/// `reject`.
///
/// # Safety
/// Both must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strcspn(s: *const c_char, reject: *const c_char) -> usize {
    // SAFETY: forwarded from the caller.
    unsafe {
        if *reject == 0 {
            return strlen(s);
        }
        if *reject.add(1) == 0 {
            return search::strchrnul(s as *const u8, *reject as u8);
        }
        let set = ByteSet::from_cstr(reject);
        let mut i = 0;
        while *s.add(i) != 0 && !set.contains(*s.add(i) as u8) {
            i += 1;
        }
        i
    }
}

/// `strpbrk(3)`.
///
/// # Safety
/// Both must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strpbrk(s: *const c_char, accept: *const c_char) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe {
        let p = s.add(strcspn(s, accept));
        if *p != 0 {
            p as *mut c_char
        } else {
            ptr::null_mut()
        }
    }
}

/// `strtok_r(3)`.
///
/// # Safety
/// `s` (or `*save`) and `delim` must be NUL-terminated; `save` must be a
/// valid pointer.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strtok_r(
    s: *mut c_char,
    delim: *const c_char,
    save: *mut *mut c_char,
) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe {
        let mut s = if s.is_null() { *save } else { s };
        if s.is_null() {
            return ptr::null_mut();
        }
        s = s.add(strspn(s, delim));
        if *s == 0 {
            *save = ptr::null_mut();
            return ptr::null_mut();
        }
        let token = s;
        s = s.add(strcspn(s, delim));
        if *s != 0 {
            *s = 0;
            *save = s.add(1);
        } else {
            *save = ptr::null_mut();
        }
        token
    }
}

/// Per-thread state of `strtok`.
///
/// # Safety
/// The current thread's TCB is always valid.
#[cfg(not(test))]
unsafe fn strtok_save() -> *mut *mut c_char {
    // SAFETY: caller contract.
    unsafe { &raw mut (*crate::thread::current()).strtok_save }
}

/// `strtok(3)`.
///
/// # Safety
/// As for [`strtok_r`].
#[cfg(not(test))]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn strtok(s: *mut c_char, delim: *const c_char) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe { strtok_r(s, delim, strtok_save()) }
}

/// `strsep(3)`.
///
/// # Safety
/// `*s` and `delim` must be NUL-terminated or `*s` NULL.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strsep(s: *mut *mut c_char, delim: *const c_char) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe {
        let start = *s;
        if start.is_null() {
            return ptr::null_mut();
        }
        let end = start.add(strcspn(start, delim));
        if *end != 0 {
            *end = 0;
            *s = end.add(1);
        } else {
            *s = ptr::null_mut();
        }
        start
    }
}

/// `strerror(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn strerror(num: c_int) -> *mut c_char {
    match crate::errno::description_cstr(num) {
        Some(s) => s.as_ptr() as *mut c_char,
        None => {
            // SAFETY: the TCB is valid for the life of the thread.
            let buf = unsafe { &mut (*crate::thread::current()).strerror_buf };
            let mut w = crate::fmt::SliceWriter::new(buf);
            let _ = core::fmt::write(&mut w, format_args!("Unknown error {num}"));
            let len = w.len();
            buf[len] = 0;
            buf.as_mut_ptr() as *mut c_char
        }
    }
}

/// `strerror_r(3)` (the POSIX variant returning an error number).
///
/// # Safety
/// `buf` must be valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strerror_r(num: c_int, buf: *mut c_char, n: usize) -> c_int {
    // SAFETY: forwarded from the caller.
    unsafe {
        let msg = strerror(num);
        let len = strlen(msg);
        if n == 0 {
            return crate::errno::Errno::ERANGE.0;
        }
        let copy = len.min(n - 1);
        memmove(buf as *mut c_void, msg as *const c_void, copy);
        *buf.add(copy) = 0;
        if copy < len {
            crate::errno::Errno::ERANGE.0
        } else {
            0
        }
    }
}

/// `strcasecmp(3)`.
///
/// # Safety
/// Both must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strcasecmp(a: *const c_char, b: *const c_char) -> c_int {
    // SAFETY: forwarded from the caller.
    unsafe { strncasecmp(a, b, usize::MAX) }
}

/// `strncasecmp(3)`.
///
/// # Safety
/// Both must be NUL-terminated or readable for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strncasecmp(a: *const c_char, b: *const c_char, n: usize) -> c_int {
    // SAFETY: forwarded from the caller.
    unsafe {
        let mut i = 0;
        while i < n {
            let x = (*a.add(i) as u8).to_ascii_lowercase();
            let y = (*b.add(i) as u8).to_ascii_lowercase();
            if x != y || x == 0 {
                return x as c_int - y as c_int;
            }
            i += 1;
        }
        0
    }
}

/// `strdup(3)`.
///
/// # Safety
/// `s` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strdup(s: *const c_char) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe {
        let len = strlen(s);
        let p = crate::malloc::alloc(len + 1) as *mut c_char;
        if !p.is_null() {
            memcpy(p as *mut c_void, s as *const c_void, len + 1);
        }
        p
    }
}

/// `strndup(3)`.
///
/// # Safety
/// `s` must be NUL-terminated or readable for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn strndup(s: *const c_char, n: usize) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    unsafe {
        let len = strnlen(s, n);
        let p = crate::malloc::alloc(len + 1) as *mut c_char;
        if !p.is_null() {
            memcpy(p as *mut c_void, s as *const c_void, len);
            *p.add(len) = 0;
        }
        p
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::{CStr, CString};

    fn c(s: &str) -> CString {
        CString::new(s).unwrap()
    }

    unsafe fn cstr<'a>(p: *const c_char) -> &'a str {
        // SAFETY: test strings are NUL-terminated.
        unsafe { CStr::from_ptr(p).to_str().unwrap() }
    }

    #[test]
    fn copies() {
        let src = c("hello");
        let mut buf = [0x55 as c_char; 16];
        // SAFETY: buffers are large enough.
        unsafe {
            assert_eq!(strcpy(buf.as_mut_ptr(), src.as_ptr()), buf.as_mut_ptr());
            assert_eq!(cstr(buf.as_ptr()), "hello");
            assert_eq!(
                stpcpy(buf.as_mut_ptr(), src.as_ptr()),
                buf.as_mut_ptr().add(5)
            );
            buf.fill(0x55);
            strncpy(buf.as_mut_ptr(), src.as_ptr(), 8);
            assert_eq!(&buf[..8], &[104, 101, 108, 108, 111, 0, 0, 0]);
            assert_eq!(buf[8], 0x55);
            strncpy(buf.as_mut_ptr(), src.as_ptr(), 3);
            assert_eq!(&buf[..4], &[104, 101, 108, 108]);
            buf.fill(0);
            strcat(buf.as_mut_ptr(), src.as_ptr());
            strcat(buf.as_mut_ptr(), src.as_ptr());
            assert_eq!(cstr(buf.as_ptr()), "hellohello");
            strncat(buf.as_mut_ptr(), src.as_ptr(), 2);
            assert_eq!(cstr(buf.as_ptr()), "hellohellohe");
            assert_eq!(strlcpy(buf.as_mut_ptr(), src.as_ptr(), 3), 5);
            assert_eq!(cstr(buf.as_ptr()), "he");
            assert_eq!(strlcpy(buf.as_mut_ptr(), src.as_ptr(), 0), 5);
            assert_eq!(cstr(buf.as_ptr()), "he");
            assert_eq!(strlcat(buf.as_mut_ptr(), src.as_ptr(), 6), 7);
            assert_eq!(cstr(buf.as_ptr()), "hehel");
            assert_eq!(strlcat(buf.as_mut_ptr(), src.as_ptr(), 2), 7);
            assert_eq!(cstr(buf.as_ptr()), "hehel");
        }
    }

    #[test]
    fn searches() {
        let s = c("hello world");
        // SAFETY: NUL-terminated.
        unsafe {
            let p = s.as_ptr();
            assert_eq!(strchr(p, b'o' as c_int), p.add(4) as *mut c_char);
            assert_eq!(strrchr(p, b'o' as c_int), p.add(7) as *mut c_char);
            assert_eq!(strchr(p, 0), p.add(11) as *mut c_char);
            assert_eq!(strrchr(p, 0), p.add(11) as *mut c_char);
            assert!(strchr(p, b'z' as c_int).is_null());
            assert!(strrchr(p, b'z' as c_int).is_null());
            assert_eq!(strchrnul(p, b'z' as c_int), p.add(11) as *mut c_char);
            assert_eq!(strstr(p, c("o w").as_ptr()), p.add(4) as *mut c_char);
            assert_eq!(strstr(p, c("").as_ptr()), p as *mut c_char);
            assert!(strstr(p, c("worlds").as_ptr()).is_null());
            assert_eq!(strspn(p, c("hel").as_ptr()), 4);
            assert_eq!(strcspn(p, c("wd").as_ptr()), 6);
            assert_eq!(strcspn(p, c("").as_ptr()), 11);
            assert_eq!(strcspn(p, c("o").as_ptr()), 4);
            assert_eq!(strpbrk(p, c("dw").as_ptr()), p.add(6) as *mut c_char);
            assert!(strpbrk(p, c("xyz").as_ptr()).is_null());
        }
    }

    #[test]
    fn tokenising() {
        let mut buf = *b"  a,b,,c  \0";
        let delim = c(", ");
        let mut save = ptr::null_mut();
        // SAFETY: NUL-terminated.
        unsafe {
            let p = buf.as_mut_ptr() as *mut c_char;
            assert_eq!(cstr(strtok_r(p, delim.as_ptr(), &mut save)), "a");
            assert_eq!(
                cstr(strtok_r(ptr::null_mut(), delim.as_ptr(), &mut save)),
                "b"
            );
            assert_eq!(
                cstr(strtok_r(ptr::null_mut(), delim.as_ptr(), &mut save)),
                "c"
            );
            assert!(strtok_r(ptr::null_mut(), delim.as_ptr(), &mut save).is_null());
            assert!(strtok_r(ptr::null_mut(), delim.as_ptr(), &mut save).is_null());
        }
        let mut buf = *b"a,b,,c\0";
        let mut s = buf.as_mut_ptr() as *mut c_char;
        let delim = c(",");
        // SAFETY: NUL-terminated.
        unsafe {
            assert_eq!(cstr(strsep(&mut s, delim.as_ptr())), "a");
            assert_eq!(cstr(strsep(&mut s, delim.as_ptr())), "b");
            assert_eq!(cstr(strsep(&mut s, delim.as_ptr())), "");
            assert_eq!(cstr(strsep(&mut s, delim.as_ptr())), "c");
            assert!(strsep(&mut s, delim.as_ptr()).is_null());
        }
    }

    #[test]
    fn dup() {
        // SAFETY: NUL-terminated inputs, blocks freed once.
        unsafe {
            let p = strdup(c("hello").as_ptr());
            assert_eq!(cstr(p), "hello");
            crate::malloc::dealloc(p as *mut u8);
            let p = strndup(c("hello").as_ptr(), 3);
            assert_eq!(cstr(p), "hel");
            crate::malloc::dealloc(p as *mut u8);
            let p = strndup(c("hello").as_ptr(), 30);
            assert_eq!(cstr(p), "hello");
            crate::malloc::dealloc(p as *mut u8);
        }
    }

    #[test]
    fn errors_and_case() {
        // SAFETY: strerror returns NUL-terminated strings.
        unsafe {
            assert_eq!(cstr(strerror(2)), "No such file or directory");
            assert_eq!(cstr(strerror(9999)), "Unknown error 9999");
            assert_eq!(cstr(strerror(-1)), "Unknown error -1");
            let mut buf = [0 as c_char; 8];
            assert_eq!(
                strerror_r(2, buf.as_mut_ptr(), 8),
                crate::errno::Errno::ERANGE.0
            );
            assert_eq!(cstr(buf.as_ptr()), "No such");
            assert_eq!(
                strerror_r(2, buf.as_mut_ptr(), 0),
                crate::errno::Errno::ERANGE.0
            );
            let mut buf = [0 as c_char; 64];
            assert_eq!(strerror_r(2, buf.as_mut_ptr(), 64), 0);
            assert_eq!(strcasecmp(c("Hello").as_ptr(), c("hELLO").as_ptr()), 0);
            assert!(strcasecmp(c("Hello").as_ptr(), c("hELLOx").as_ptr()) < 0);
            assert_eq!(strncasecmp(c("Hello").as_ptr(), c("hELLOx").as_ptr(), 5), 0);
            assert_eq!(strcoll(c("a").as_ptr(), c("a").as_ptr()), 0);
            let mut buf = [0 as c_char; 4];
            assert_eq!(strxfrm(buf.as_mut_ptr(), c("abcdef").as_ptr(), 4), 6);
            assert_eq!(buf[0], 0);
            assert_eq!(strxfrm(buf.as_mut_ptr(), c("ab").as_ptr(), 4), 2);
            assert_eq!(cstr(buf.as_ptr()), "ab");
        }
    }
}
