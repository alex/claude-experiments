//! `<pwd.h>` and `<grp.h>`: lookups in `/etc/passwd` and `/etc/group`.

use crate::c_char;
use crate::errno::Errno;
use crate::stdio;
use core::ffi::{c_int, c_uint};
use core::ptr;

/// `struct passwd`.
#[allow(missing_docs)]
#[repr(C)]
pub struct Passwd {
    pub pw_name: *mut c_char,
    pub pw_passwd: *mut c_char,
    pub pw_uid: c_uint,
    pub pw_gid: c_uint,
    pub pw_gecos: *mut c_char,
    pub pw_dir: *mut c_char,
    pub pw_shell: *mut c_char,
}

/// `struct group`.
#[allow(missing_docs)]
#[repr(C)]
pub struct Group {
    pub gr_name: *mut c_char,
    pub gr_passwd: *mut c_char,
    pub gr_gid: c_uint,
    pub gr_mem: *mut *mut c_char,
}

/// What to look for.
enum Key<'a> {
    Name(&'a [u8]),
    Id(c_uint),
}

/// Reads `file` line by line and returns the first line whose first
/// field (name) or `id_field`-th field (numeric id) matches `key`. The
/// line is copied into `buf` (NUL-terminated) and returned as a slice.
fn find_line<'a>(
    file: &core::ffi::CStr,
    key: &Key,
    id_field: usize,
    buf: &'a mut [u8],
) -> Result<Option<&'a mut [u8]>, Errno> {
    // SAFETY: NUL-terminated literals.
    let f = unsafe { stdio::fopen(file.as_ptr(), c"re".as_ptr()) };
    if f.is_null() {
        return Err(Errno::get());
    }
    // SAFETY: the stream is open.
    let mut g = unsafe { stdio::lock(f) };
    let mut line = [0u8; 1024];
    let mut result = None;
    loop {
        let mut len = 0;
        let mut eof = false;
        loop {
            match g.getc() {
                Some(b'\n') => break,
                Some(b) => {
                    if len < line.len() {
                        line[len] = b;
                        len += 1;
                    }
                }
                None => {
                    eof = true;
                    break;
                }
            }
        }
        if len > 0 && len < line.len() {
            let l = &line[..len];
            let mut fields = l.split(|&b| b == b':');
            let name = fields.next().unwrap_or(b"");
            let matched = match key {
                Key::Name(n) => name == *n,
                Key::Id(id) => {
                    l.split(|&b| b == b':').nth(id_field).and_then(parse_uint) == Some(*id)
                }
            };
            if matched {
                if len + 1 > buf.len() {
                    drop(g);
                    // SAFETY: the stream is open.
                    unsafe { stdio::fclose(f) };
                    return Err(Errno::ERANGE);
                }
                buf[..len].copy_from_slice(l);
                buf[len] = 0;
                result = Some(len);
                break;
            }
        }
        if eof {
            break;
        }
    }
    drop(g);
    // SAFETY: the stream is open.
    unsafe { stdio::fclose(f) };
    Ok(result.map(move |len| &mut buf[..len]))
}

fn parse_uint(s: &[u8]) -> Option<c_uint> {
    if s.is_empty() {
        return None;
    }
    let mut v: c_uint = 0;
    for &b in s {
        v = v
            .checked_mul(10)?
            .checked_add((b as char).to_digit(10)? as c_uint)?;
    }
    Some(v)
}

/// Splits the NUL-terminated line in `buf` into fields, replacing ':'
/// with NUL, and returns pointers to up to `N` fields.
fn split_fields<const N: usize>(buf: &mut [u8]) -> [*mut c_char; N] {
    let mut out = [ptr::null_mut(); N];
    let mut start = 0;
    let mut n = 0;
    for i in 0..=buf.len() {
        if i == buf.len() || buf[i] == b':' {
            if n < N {
                out[n] = buf[start..].as_mut_ptr() as *mut c_char;
                n += 1;
            }
            if i < buf.len() {
                buf[i] = 0;
            }
            start = i + 1;
        }
    }
    out
}

/// Shared implementation of `getpwnam_r`/`getpwuid_r`.
///
/// # Safety
/// `pwd`, `result` must be valid; `buf` valid for `buflen` bytes.
unsafe fn getpw(
    key: Key,
    pwd: *mut Passwd,
    buf: *mut c_char,
    buflen: usize,
    result: *mut *mut Passwd,
) -> c_int {
    // SAFETY: caller contract.
    unsafe { *result = ptr::null_mut() };
    // SAFETY: caller contract.
    let storage = unsafe { core::slice::from_raw_parts_mut(buf as *mut u8, buflen) };
    match find_line(c"/etc/passwd", &key, 2, storage) {
        Err(e) => e.0,
        Ok(None) => 0,
        Ok(Some(line)) => {
            let f = split_fields::<7>(line);
            // SAFETY: the fields are NUL-terminated inside `buf`.
            let num = |p: *mut c_char| unsafe {
                let len = crate::string::search::strlen(p as *const u8);
                parse_uint(core::slice::from_raw_parts(p as *const u8, len))
            };
            if f[6].is_null() {
                return Errno::EINVAL.0;
            }
            // A malformed id must not turn into root's.
            let (Some(uid), Some(gid)) = (num(f[2]), num(f[3])) else {
                return Errno::EINVAL.0;
            };
            // SAFETY: caller contract.
            unsafe {
                *pwd = Passwd {
                    pw_name: f[0],
                    pw_passwd: f[1],
                    pw_uid: uid,
                    pw_gid: gid,
                    pw_gecos: f[4],
                    pw_dir: f[5],
                    pw_shell: f[6],
                };
                *result = pwd;
            }
            0
        }
    }
}

/// `getpwnam_r(3)`.
///
/// # Safety
/// `name` must be NUL-terminated; other pointers valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getpwnam_r(
    name: *const c_char,
    pwd: *mut Passwd,
    buf: *mut c_char,
    buflen: usize,
    result: *mut *mut Passwd,
) -> c_int {
    // SAFETY: caller contract.
    let n = unsafe {
        core::slice::from_raw_parts(
            name as *const u8,
            crate::string::search::strlen(name as *const u8),
        )
    };
    // SAFETY: forwarded.
    unsafe { getpw(Key::Name(n), pwd, buf, buflen, result) }
}

/// `getpwuid_r(3)`.
///
/// # Safety
/// All pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getpwuid_r(
    uid: c_uint,
    pwd: *mut Passwd,
    buf: *mut c_char,
    buflen: usize,
    result: *mut *mut Passwd,
) -> c_int {
    // SAFETY: forwarded.
    unsafe { getpw(Key::Id(uid), pwd, buf, buflen, result) }
}

struct PwStatic {
    pwd: Passwd,
    grp: Group,
    members: [*mut c_char; 64],
    buf: [u8; 1024],
}
// SAFETY: guarded by the mutex.
unsafe impl Send for PwStatic {}
static STATIC: crate::sync::Mutex<PwStatic> = crate::sync::Mutex::new(PwStatic {
    pwd: Passwd {
        pw_name: ptr::null_mut(),
        pw_passwd: ptr::null_mut(),
        pw_uid: 0,
        pw_gid: 0,
        pw_gecos: ptr::null_mut(),
        pw_dir: ptr::null_mut(),
        pw_shell: ptr::null_mut(),
    },
    grp: Group {
        gr_name: ptr::null_mut(),
        gr_passwd: ptr::null_mut(),
        gr_gid: 0,
        gr_mem: ptr::null_mut(),
    },
    members: [ptr::null_mut(); 64],
    buf: [0; 1024],
});

/// `getpwnam(3)` (uses a static buffer).
///
/// # Safety
/// `name` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getpwnam(name: *const c_char) -> *mut Passwd {
    let mut s = STATIC.lock();
    let s = &mut *s;
    let mut result = ptr::null_mut();
    // SAFETY: forwarded; the static buffers are valid.
    let r = unsafe {
        getpwnam_r(
            name,
            &mut s.pwd,
            s.buf.as_mut_ptr() as *mut c_char,
            s.buf.len(),
            &mut result,
        )
    };
    if r != 0 {
        Errno(r).set();
    }
    result
}

/// `getpwuid(3)` (uses a static buffer).
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn getpwuid(uid: c_uint) -> *mut Passwd {
    let mut s = STATIC.lock();
    let s = &mut *s;
    let mut result = ptr::null_mut();
    // SAFETY: the static buffers are valid.
    let r = unsafe {
        getpwuid_r(
            uid,
            &mut s.pwd,
            s.buf.as_mut_ptr() as *mut c_char,
            s.buf.len(),
            &mut result,
        )
    };
    if r != 0 {
        Errno(r).set();
    }
    result
}

/// Shared implementation of `getgrnam_r`/`getgrgid_r`. The member
/// pointer array is placed in `buf` after the line.
///
/// # Safety
/// `grp`, `result` must be valid; `buf` valid for `buflen` bytes.
unsafe fn getgr(
    key: Key,
    grp: *mut Group,
    buf: *mut c_char,
    buflen: usize,
    result: *mut *mut Group,
) -> c_int {
    // SAFETY: caller contract.
    unsafe { *result = ptr::null_mut() };
    // SAFETY: caller contract.
    let storage = unsafe { core::slice::from_raw_parts_mut(buf as *mut u8, buflen) };
    let line_len = match find_line(c"/etc/group", &key, 2, storage) {
        Err(e) => return e.0,
        Ok(None) => return 0,
        Ok(Some(line)) => line.len(),
    };
    let (line, rest) = storage.split_at_mut(line_len + 1);
    let f = split_fields::<4>(&mut line[..line_len]);
    if f[3].is_null() {
        return Errno::EINVAL.0;
    }
    // Member list: pointers (8-byte aligned) after the line.
    // SAFETY: the members field is NUL-terminated inside `buf`.
    let members = unsafe {
        core::slice::from_raw_parts_mut(
            f[3] as *mut u8,
            crate::string::search::strlen(f[3] as *const u8),
        )
    };
    let count = if members.is_empty() {
        0
    } else {
        members.iter().filter(|&&b| b == b',').count() + 1
    };
    let align = rest.as_ptr().align_offset(8);
    if align + (count + 1) * 8 > rest.len() {
        return Errno::ERANGE.0;
    }
    let list = rest[align..].as_mut_ptr() as *mut *mut c_char;
    let mut start = 0;
    let mut n = 0;
    for i in 0..=members.len() {
        if i == members.len() || members[i] == b',' {
            if !members.is_empty() {
                // SAFETY: room for `count + 1` pointers.
                unsafe { *list.add(n) = members[start..].as_mut_ptr() as *mut c_char };
                n += 1;
            }
            if i < members.len() {
                members[i] = 0;
            }
            start = i + 1;
        }
    }
    // SAFETY: as above; caller contract for the out-pointers.
    unsafe {
        *list.add(n) = ptr::null_mut();
        let gid = {
            let len = crate::string::search::strlen(f[2] as *const u8);
            match parse_uint(core::slice::from_raw_parts(f[2] as *const u8, len)) {
                Some(g) => g,
                None => return Errno::EINVAL.0,
            }
        };
        *grp = Group {
            gr_name: f[0],
            gr_passwd: f[1],
            gr_gid: gid,
            gr_mem: list,
        };
        *result = grp;
    }
    0
}

/// `getgrnam_r(3)`.
///
/// # Safety
/// `name` must be NUL-terminated; other pointers valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getgrnam_r(
    name: *const c_char,
    grp: *mut Group,
    buf: *mut c_char,
    buflen: usize,
    result: *mut *mut Group,
) -> c_int {
    // SAFETY: caller contract.
    let n = unsafe {
        core::slice::from_raw_parts(
            name as *const u8,
            crate::string::search::strlen(name as *const u8),
        )
    };
    // SAFETY: forwarded.
    unsafe { getgr(Key::Name(n), grp, buf, buflen, result) }
}

/// `getgrgid_r(3)`.
///
/// # Safety
/// All pointers must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getgrgid_r(
    gid: c_uint,
    grp: *mut Group,
    buf: *mut c_char,
    buflen: usize,
    result: *mut *mut Group,
) -> c_int {
    // SAFETY: forwarded.
    unsafe { getgr(Key::Id(gid), grp, buf, buflen, result) }
}

/// `getgrnam(3)` (uses a static buffer).
///
/// # Safety
/// `name` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getgrnam(name: *const c_char) -> *mut Group {
    let mut s = STATIC.lock();
    let s = &mut *s;
    let _ = &s.members;
    let mut result = ptr::null_mut();
    // SAFETY: forwarded; the static buffers are valid.
    let r = unsafe {
        getgrnam_r(
            name,
            &mut s.grp,
            s.buf.as_mut_ptr() as *mut c_char,
            s.buf.len(),
            &mut result,
        )
    };
    if r != 0 {
        Errno(r).set();
    }
    result
}

/// `getgrgid(3)` (uses a static buffer).
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn getgrgid(gid: c_uint) -> *mut Group {
    let mut s = STATIC.lock();
    let s = &mut *s;
    let mut result = ptr::null_mut();
    // SAFETY: the static buffers are valid.
    let r = unsafe {
        getgrgid_r(
            gid,
            &mut s.grp,
            s.buf.as_mut_ptr() as *mut c_char,
            s.buf.len(),
            &mut result,
        )
    };
    if r != 0 {
        Errno(r).set();
    }
    result
}

/// `getlogin(3)`: from `LOGNAME`, else the passwd entry of the real uid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn getlogin() -> *mut c_char {
    // SAFETY: NUL-terminated literal.
    let env = unsafe { crate::stdlib::env::getenv(c"LOGNAME".as_ptr()) };
    if !env.is_null() {
        return env;
    }
    let p = getpwuid(crate::unistd::getuid());
    if p.is_null() {
        return ptr::null_mut();
    }
    // SAFETY: a valid entry.
    unsafe { (*p).pw_name }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CStr;

    #[test]
    fn root_lookups() {
        // Every Linux box has root in /etc/passwd and /etc/group.
        let p = getpwuid(0);
        assert!(!p.is_null());
        // SAFETY: valid entry.
        unsafe {
            assert_eq!(CStr::from_ptr((*p).pw_name).to_bytes(), b"root");
            assert_eq!((*p).pw_uid, 0);
            assert_eq!(CStr::from_ptr((*p).pw_dir).to_bytes(), b"/root");
            let q = getpwnam(c"root".as_ptr());
            assert!(!q.is_null() && (*q).pw_uid == 0);
            assert!(getpwnam(c"no-such-user-xyz".as_ptr()).is_null());
            let g = getgrgid(0);
            assert!(!g.is_null());
            assert_eq!(CStr::from_ptr((*g).gr_name).to_bytes(), b"root");
            assert!(!(*g).gr_mem.is_null());
            let g = getgrnam(c"root".as_ptr());
            assert!(!g.is_null() && (*g).gr_gid == 0);
            let mut small = [0 as c_char; 8];
            let mut pw = core::mem::MaybeUninit::<Passwd>::zeroed();
            let mut res = ptr::null_mut();
            assert_eq!(
                getpwuid_r(0, pw.as_mut_ptr(), small.as_mut_ptr(), 8, &mut res),
                Errno::ERANGE.0
            );
        }
    }
}
