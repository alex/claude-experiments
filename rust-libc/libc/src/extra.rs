//! Smaller pieces of `<stdio.h>`, `<stdlib.h>`, `<unistd.h>`, `<sched.h>`
//! and a few Linux-specific headers that do not warrant a module each.

use crate::c_char;
use crate::errno::{CReturn, CReturnOr, Errno};
use crate::stdio::File;
use crate::sync::Mutex;
use crate::sys::{self, Timespec};
use core::ffi::{c_int, c_long, c_uint, c_ulong, c_ushort, c_void};
use core::ptr;

// ---------------------------------------------------------------------
// popen / pclose.

/// `popen(3)`: the child's pid is kept in the stream's cookie.
///
/// # Safety
/// `cmd` and `mode` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn popen(cmd: *const c_char, mode: *const c_char) -> *mut File {
    // SAFETY: caller contract.
    let m = unsafe { *mode } as u8;
    if m != b'r' && m != b'w' {
        Errno::EINVAL.set();
        return ptr::null_mut();
    }
    let mut fds = [0 as c_int; 2];
    // SAFETY: valid array.
    if unsafe { crate::unistd::pipe2(fds.as_mut_ptr(), sys::O_CLOEXEC) } < 0 {
        return ptr::null_mut();
    }
    let (parent_end, child_end, child_fd) = if m == b'r' {
        (fds[0], fds[1], 1)
    } else {
        (fds[1], fds[0], 0)
    };
    let pid = crate::process::fork();
    if pid < 0 {
        let _ = sys::close(fds[0]);
        let _ = sys::close(fds[1]);
        return ptr::null_mut();
    }
    if pid == 0 {
        // SAFETY: child: wire the pipe to stdin/stdout and run the shell.
        unsafe {
            if crate::unistd::dup2(child_end, child_fd) < 0 {
                crate::exit::_exit(127);
            }
            let argv = [c"sh".as_ptr(), c"-c".as_ptr(), cmd, ptr::null()];
            crate::process::execve(
                c"/bin/sh".as_ptr(),
                argv.as_ptr(),
                crate::start::environ as *const *const c_char,
            );
            crate::exit::_exit(127);
        }
    }
    let _ = sys::close(child_end);
    // SAFETY: literal modes.
    let f = unsafe {
        crate::stdio::fdopen(
            parent_end,
            if m == b'r' {
                c"r".as_ptr()
            } else {
                c"w".as_ptr()
            },
        )
    };
    if f.is_null() {
        let _ = sys::close(parent_end);
        return f;
    }
    // SAFETY: the stream is ours; the cookie is unused for fd streams.
    unsafe { (*f).cookie = pid as usize as *mut c_void };
    f
}

/// `pclose(3)`.
///
/// # Safety
/// `f` must come from `popen`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pclose(f: *mut File) -> c_int {
    // SAFETY: caller contract.
    let pid = unsafe { (*f).cookie } as usize as c_int;
    // SAFETY: forwarded.
    unsafe { crate::stdio::fclose(f) };
    let mut status = 0;
    loop {
        // SAFETY: valid pointer.
        match unsafe { sys::wait4(pid, &mut status, 0, ptr::null_mut()) } {
            Ok(_) => return status,
            Err(Errno::EINTR) => {}
            Err(e) => {
                e.set();
                return -1;
            }
        }
    }
}

/// `ctermid(3)`.
///
/// # Safety
/// `s` must be null or valid for `L_ctermid` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn ctermid(s: *mut c_char) -> *mut c_char {
    static NAME: [u8; 9] = *b"/dev/tty\0";
    if s.is_null() {
        return NAME.as_ptr() as *mut c_char;
    }
    // SAFETY: caller contract.
    unsafe { ptr::copy_nonoverlapping(NAME.as_ptr(), s as *mut u8, 9) };
    s
}

// ---------------------------------------------------------------------
// rand48.

struct Rand48 {
    x: [u16; 3],
    a: [u16; 3],
    c: u16,
}

static RAND48: Mutex<Rand48> = Mutex::new(Rand48 {
    x: [0x330e, 0xabcd, 0x1234],
    a: [0xe66d, 0xdeec, 0x5],
    c: 0xb,
});

fn step48(x: &mut [u16; 3], a: &[u16; 3], c: u16) -> u64 {
    let xv = (x[0] as u64) | (x[1] as u64) << 16 | (x[2] as u64) << 32;
    let av = (a[0] as u64) | (a[1] as u64) << 16 | (a[2] as u64) << 32;
    let next = (xv.wrapping_mul(av).wrapping_add(c as u64)) & 0xffff_ffff_ffff;
    x[0] = next as u16;
    x[1] = (next >> 16) as u16;
    x[2] = (next >> 32) as u16;
    next
}

/// `erand48(3)`.
///
/// # Safety
/// `x` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn erand48(x: *mut u16) -> f64 {
    let st = RAND48.lock();
    // SAFETY: caller contract.
    let v = unsafe { step48(&mut *(x as *mut [u16; 3]), &st.a, st.c) };
    v as f64 / 281_474_976_710_656.0
}

/// `drand48(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn drand48() -> f64 {
    let mut st = RAND48.lock();
    let (a, c) = (st.a, st.c);
    step48(&mut st.x, &a, c) as f64 / 281_474_976_710_656.0
}

/// `nrand48(3)`.
///
/// # Safety
/// `x` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn nrand48(x: *mut u16) -> c_long {
    let st = RAND48.lock();
    // SAFETY: caller contract.
    (unsafe { step48(&mut *(x as *mut [u16; 3]), &st.a, st.c) } >> 17) as c_long
}

/// `lrand48(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn lrand48() -> c_long {
    let mut st = RAND48.lock();
    let (a, c) = (st.a, st.c);
    (step48(&mut st.x, &a, c) >> 17) as c_long
}

/// `jrand48(3)`.
///
/// # Safety
/// `x` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn jrand48(x: *mut u16) -> c_long {
    let st = RAND48.lock();
    // SAFETY: caller contract.
    (unsafe { step48(&mut *(x as *mut [u16; 3]), &st.a, st.c) } >> 16) as i32 as c_long
}

/// `mrand48(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn mrand48() -> c_long {
    let mut st = RAND48.lock();
    let (a, c) = (st.a, st.c);
    (step48(&mut st.x, &a, c) >> 16) as i32 as c_long
}

/// `srand48(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn srand48(seed: c_long) {
    let mut st = RAND48.lock();
    st.x = [0x330e, seed as u16, (seed >> 16) as u16];
    st.a = [0xe66d, 0xdeec, 0x5];
    st.c = 0xb;
}

/// `seed48(3)`.
///
/// # Safety
/// `seed` must point to three shorts.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn seed48(seed: *mut u16) -> *mut u16 {
    static mut OLD: [u16; 3] = [0; 3];
    let mut st = RAND48.lock();
    // SAFETY: caller contract; OLD is only used under the lock.
    unsafe {
        OLD = st.x;
        st.x = *(seed as *const [u16; 3]);
        st.a = [0xe66d, 0xdeec, 0x5];
        st.c = 0xb;
        &raw mut OLD as *mut u16
    }
}

/// `lcong48(3)`.
///
/// # Safety
/// `param` must point to seven shorts.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn lcong48(param: *const u16) {
    let mut st = RAND48.lock();
    // SAFETY: caller contract.
    unsafe {
        st.x = [*param, *param.add(1), *param.add(2)];
        st.a = [*param.add(3), *param.add(4), *param.add(5)];
        st.c = *param.add(6);
    }
}

// ---------------------------------------------------------------------
// stdlib odds and ends.

static QUICK_EXIT: Mutex<([Option<extern "C" fn()>; 32], usize)> = Mutex::new(([None; 32], 0));

/// `at_quick_exit(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn at_quick_exit(func: extern "C" fn()) -> c_int {
    let mut q = QUICK_EXIT.lock();
    if q.1 == 32 {
        return -1;
    }
    let n = q.1;
    q.0[n] = Some(func);
    q.1 += 1;
    0
}

/// `quick_exit(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn quick_exit(status: c_int) -> ! {
    loop {
        let f = {
            let mut q = QUICK_EXIT.lock();
            if q.1 == 0 {
                break;
            }
            q.1 -= 1;
            let n = q.1;
            q.0[n].take()
        };
        if let Some(f) = f {
            f();
        }
    }
    crate::exit::_exit(status)
}

/// `secure_getenv(3)`: NULL when the process is set-uid/set-gid.
///
/// # Safety
/// `name` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn secure_getenv(name: *const c_char) -> *mut c_char {
    if crate::start::auxval(crate::start::auxv::AT_SECURE).unwrap_or(0) != 0 {
        return ptr::null_mut();
    }
    // SAFETY: forwarded.
    unsafe { crate::stdlib::env::getenv(name) }
}

/// `getloadavg(3)`.
///
/// # Safety
/// `out` must be valid for `n` doubles.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getloadavg(out: *mut f64, n: c_int) -> c_int {
    #[repr(C)]
    struct SysInfo {
        uptime: i64,
        loads: [u64; 3],
        rest: [u8; 112 - 32],
    }
    let mut info = SysInfo {
        uptime: 0,
        loads: [0; 3],
        rest: [0; 80],
    };
    // SAFETY: the struct is large enough for the kernel's.
    if unsafe { crate::fs::sysinfo(&mut info as *mut SysInfo as *mut c_void) } < 0 {
        return -1;
    }
    let n = n.clamp(0, 3);
    for i in 0..n as usize {
        // SAFETY: caller contract.
        unsafe { *out.add(i) = info.loads[i] as f64 / 65536.0 };
    }
    n
}

/// `getsubopt(3)`.
///
/// # Safety
/// `optionp` must point to a writable NUL-terminated string; `tokens` a
/// NULL-terminated array; `valuep` valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getsubopt(
    optionp: *mut *mut c_char,
    tokens: *const *const c_char,
    valuep: *mut *mut c_char,
) -> c_int {
    // SAFETY: caller contract.
    unsafe {
        let s = *optionp;
        *valuep = ptr::null_mut();
        if s.is_null() || *s == 0 {
            return -1;
        }
        let len = crate::string::search::strlen(s as *const u8);
        let bytes = core::slice::from_raw_parts(s as *const u8, len);
        let end = crate::string::search::memchr(bytes, b',').unwrap_or(len);
        let item = &bytes[..end];
        let (name, value) = match crate::string::search::memchr(item, b'=') {
            Some(eq) => (&item[..eq], Some(eq + 1)),
            None => (item, None),
        };
        // Terminate this item and advance.
        if end < len {
            *s.add(end) = 0;
            *optionp = s.add(end + 1);
        } else {
            *optionp = s.add(len);
        }
        if let Some(v) = value {
            *s.add(v - 1) = 0;
            *valuep = s.add(v);
        }
        let mut i = 0;
        loop {
            let t = *tokens.add(i);
            if t.is_null() {
                *valuep = s;
                return -1;
            }
            let tl = crate::string::search::strlen(t as *const u8);
            if core::slice::from_raw_parts(t as *const u8, tl) == name {
                return i as c_int;
            }
            i += 1;
        }
    }
}

/// `getprogname(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn getprogname() -> *const c_char {
    // SAFETY: a plain global set at startup.
    unsafe { crate::misc::__progname }
}

// ---------------------------------------------------------------------
// unistd odds and ends.

/// `getgroups(2)`.
///
/// # Safety
/// `list` must be valid for `size` gids.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getgroups(size: c_int, list: *mut c_uint) -> c_int {
    // SAFETY: caller contract.
    let r = unsafe { crate::arch::syscall2(115, size as usize, list as usize) };
    sys::check(r).map(|v| v as c_int).c_ret_or(-1)
}

/// `setgroups(2)`.
///
/// # Safety
/// `list` must be valid for `size` gids.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn setgroups(size: usize, list: *const c_uint) -> c_int {
    // SAFETY: caller contract.
    let r = unsafe { crate::arch::syscall2(116, size, list as usize) };
    sys::check(r).map(drop).c_ret()
}

macro_rules! id3 {
    ($($(#[$doc:meta])* $name:ident($($arg:ident),*) = $nr:expr;)*) => {
        $(
            $(#[$doc])*
            ///
            /// # Safety
            /// Pointer arguments must be valid.
            #[cfg_attr(not(test), unsafe(no_mangle))]
            pub unsafe extern "C" fn $name($($arg: *mut c_uint),*) -> c_int {
                // SAFETY: caller contract.
                let r = unsafe { crate::arch::syscall3($nr, $($arg as usize),*) };
                sys::check(r).map(drop).c_ret()
            }
        )*
    };
}
id3! {
    /// `getresuid(2)`.
    getresuid(r, e, s) = 118;
    /// `getresgid(2)`.
    getresgid(r, e, s) = 120;
}

/// `setresuid(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn setresuid(r: c_uint, e: c_uint, s: c_uint) -> c_int {
    // SAFETY: no memory is involved.
    sys::check(unsafe { crate::arch::syscall3(117, r as usize, e as usize, s as usize) })
        .map(drop)
        .c_ret()
}

/// `setresgid(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn setresgid(r: c_uint, e: c_uint, s: c_uint) -> c_int {
    // SAFETY: no memory is involved.
    sys::check(unsafe { crate::arch::syscall3(119, r as usize, e as usize, s as usize) })
        .map(drop)
        .c_ret()
}

/// `setpgrp(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn setpgrp() -> c_int {
    crate::unistd::setpgid(0, 0)
}

/// `struct flock`.
#[repr(C)]
struct Flock {
    l_type: i16,
    l_whence: i16,
    l_start: i64,
    l_len: i64,
    l_pid: c_int,
}

/// `lockf(3)` over `fcntl` record locks.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn lockf(fd: c_int, cmd: c_int, len: i64) -> c_int {
    const F_ULOCK: c_int = 0;
    const F_LOCK: c_int = 1;
    const F_TLOCK: c_int = 2;
    const F_TEST: c_int = 3;
    let mut l = Flock {
        l_type: 1,
        l_whence: sys::SEEK_CUR as i16,
        l_start: 0,
        l_len: len,
        l_pid: 0,
    };
    let (fcmd, kind) = match cmd {
        F_ULOCK => (6, 2), // F_SETLK, F_UNLCK
        F_LOCK => (7, 1),  // F_SETLKW, F_WRLCK
        F_TLOCK => (6, 1), // F_SETLK, F_WRLCK
        F_TEST => (5, 1),  // F_GETLK
        _ => {
            Errno::EINVAL.set();
            return -1;
        }
    };
    l.l_type = kind;
    // SAFETY: valid flock structure.
    let r = unsafe { sys::fcntl(fd, fcmd, &mut l as *mut Flock as usize) };
    match (cmd, r) {
        (F_TEST, Ok(_)) => {
            if l.l_type == 2 || l.l_pid == sys::getpid() {
                0
            } else {
                Errno::EACCES.set();
                -1
            }
        }
        (_, Ok(_)) => 0,
        (_, Err(e)) => {
            (if e == Errno::EAGAIN { Errno::EACCES } else { e }).set();
            -1
        }
    }
}

/// `pathconf(3)`: static answers for the Linux defaults.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn pathconf(_path: *const c_char, name: c_int) -> c_long {
    fpathconf(-1, name)
}

/// `fpathconf(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn fpathconf(_fd: c_int, name: c_int) -> c_long {
    match name {
        0 => 127,   // _PC_LINK_MAX
        1 => 255,   // _PC_MAX_CANON
        2 => 255,   // _PC_MAX_INPUT
        3 => 255,   // _PC_NAME_MAX
        4 => 4096,  // _PC_PATH_MAX
        5 => 4096,  // _PC_PIPE_BUF
        6 => 1,     // _PC_CHOWN_RESTRICTED
        7 => 1,     // _PC_NO_TRUNC
        8 => 0,     // _PC_VDISABLE
        20 => 4096, // _PC_REC_XFER_ALIGN
        _ => {
            Errno::EINVAL.set();
            -1
        }
    }
}

/// `confstr(3)`: only `_CS_PATH`.
///
/// # Safety
/// `buf` must be null or valid for `len` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn confstr(name: c_int, buf: *mut c_char, len: usize) -> usize {
    let value: &[u8] = match name {
        0 => b"/bin:/usr/bin\0",
        _ => {
            Errno::EINVAL.set();
            return 0;
        }
    };
    if !buf.is_null() && len > 0 {
        let n = value.len().min(len);
        // SAFETY: caller contract.
        unsafe {
            ptr::copy_nonoverlapping(value.as_ptr(), buf as *mut u8, n);
            *buf.add(n - 1) = 0;
        }
    }
    value.len()
}

static BRK: Mutex<usize> = Mutex::new(0);

/// `brk(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn brk(addr: *mut c_void) -> c_int {
    let mut cur = BRK.lock();
    // SAFETY: the kernel validates the address.
    let r = unsafe { crate::arch::syscall1(crate::arch::nr::BRK, addr as usize) };
    if r < addr as usize {
        Errno::ENOMEM.set();
        return -1;
    }
    *cur = r;
    0
}

/// `sbrk(2)`: the allocator does not use the program break, so this is
/// available to programs that manage it themselves.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn sbrk(increment: isize) -> *mut c_void {
    let mut cur = BRK.lock();
    if *cur == 0 {
        // SAFETY: brk(0) queries the current break.
        *cur = unsafe { crate::arch::syscall1(crate::arch::nr::BRK, 0) };
    }
    let old = *cur;
    if increment == 0 {
        return old as *mut c_void;
    }
    let Some(new) = old.checked_add_signed(increment) else {
        Errno::ENOMEM.set();
        return usize::MAX as *mut c_void;
    };
    // SAFETY: the kernel validates the address.
    let r = unsafe { crate::arch::syscall1(crate::arch::nr::BRK, new) };
    if r != new {
        Errno::ENOMEM.set();
        return usize::MAX as *mut c_void;
    }
    *cur = new;
    old as *mut c_void
}

/// `swab(3)`.
///
/// # Safety
/// Both buffers must be valid for `n` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn swab(from: *const c_void, to: *mut c_void, n: isize) {
    let n = n.max(0) as usize & !1;
    let mut i = 0;
    while i < n {
        // SAFETY: caller contract.
        unsafe {
            let (a, b) = (*(from as *const u8).add(i), *(from as *const u8).add(i + 1));
            *(to as *mut u8).add(i) = b;
            *(to as *mut u8).add(i + 1) = a;
        }
        i += 2;
    }
}

/// `getdtablesize(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn getdtablesize() -> c_int {
    crate::fs::sysconf(4) as c_int
}

/// `posix_fadvise(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn posix_fadvise(fd: c_int, off: i64, len: i64, advice: c_int) -> c_int {
    // SAFETY: no memory is involved.
    let r = unsafe {
        crate::arch::syscall4(
            221,
            fd as usize,
            off as usize,
            len as usize,
            advice as usize,
        )
    };
    sys::check(r).err().map_or(0, |e| e.0)
}

/// `fallocate(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn fallocate(fd: c_int, mode: c_int, off: i64, len: i64) -> c_int {
    // SAFETY: no memory is involved.
    let r = unsafe {
        crate::arch::syscall4(285, fd as usize, mode as usize, off as usize, len as usize)
    };
    sys::check(r).map(drop).c_ret()
}

/// `posix_fallocate(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn posix_fallocate(fd: c_int, off: i64, len: i64) -> c_int {
    // SAFETY: no memory is involved.
    let r = unsafe { crate::arch::syscall4(285, fd as usize, 0, off as usize, len as usize) };
    sys::check(r).err().map_or(0, |e| e.0)
}

/// `copy_file_range(2)`.
///
/// # Safety
/// The offset pointers must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn copy_file_range(
    fd_in: c_int,
    off_in: *mut i64,
    fd_out: c_int,
    off_out: *mut i64,
    len: usize,
    flags: c_uint,
) -> isize {
    // SAFETY: caller contract.
    let r = unsafe {
        crate::arch::syscall6(
            326,
            fd_in as usize,
            off_in as usize,
            fd_out as usize,
            off_out as usize,
            len,
            flags as usize,
        )
    };
    sys::check(r).c_ret()
}

/// `sethostname(2)`.
///
/// # Safety
/// `name` must be valid for `len` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sethostname(name: *const c_char, len: usize) -> c_int {
    // SAFETY: caller contract.
    let r = unsafe { crate::arch::syscall2(170, name as usize, len) };
    sys::check(r).map(drop).c_ret()
}

/// `getdomainname(2)`.
///
/// # Safety
/// `name` must be valid for `len` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getdomainname(name: *mut c_char, len: usize) -> c_int {
    let mut u = crate::fs::Utsname {
        fields: [[0; 65]; 6],
    };
    // SAFETY: valid pointer.
    if unsafe { crate::fs::uname(&mut u as *mut crate::fs::Utsname as *mut c_void) } < 0 {
        return -1;
    }
    let dom = &u.fields[5];
    let n = dom.iter().position(|&b| b == 0).unwrap_or(65);
    if n >= len {
        Errno::EINVAL.set();
        return -1;
    }
    // SAFETY: caller contract.
    unsafe {
        ptr::copy_nonoverlapping(dom.as_ptr(), name as *mut u8, n);
        *name.add(n) = 0;
    }
    0
}

/// `ualarm(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn ualarm(value: c_uint, interval: c_uint) -> c_uint {
    #[repr(C)]
    struct Itimerval {
        interval: crate::time::Timeval,
        value: crate::time::Timeval,
    }
    let new = Itimerval {
        interval: crate::time::Timeval {
            tv_sec: (interval / 1_000_000) as i64,
            tv_usec: (interval % 1_000_000) as i64,
        },
        value: crate::time::Timeval {
            tv_sec: (value / 1_000_000) as i64,
            tv_usec: (value % 1_000_000) as i64,
        },
    };
    let mut old = Itimerval {
        interval: crate::time::Timeval::default(),
        value: crate::time::Timeval::default(),
    };
    // SAFETY: valid structures.
    if unsafe {
        crate::fs::setitimer(
            0,
            &new as *const Itimerval as *const c_void,
            &mut old as *mut Itimerval as *mut c_void,
        )
    } < 0
    {
        return c_uint::MAX;
    }
    (old.value.tv_sec * 1_000_000 + old.value.tv_usec) as c_uint
}

/// `syncfs(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn syncfs(fd: c_int) -> c_int {
    // SAFETY: no memory is involved.
    sys::check(unsafe { crate::arch::syscall1(306, fd as usize) })
        .map(drop)
        .c_ret()
}

// ---------------------------------------------------------------------
// sched.

/// `sched_getcpu(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn sched_getcpu() -> c_int {
    let mut cpu: c_uint = 0;
    // SAFETY: `cpu` is a valid local.
    if let Some(r) = unsafe { crate::vdso::getcpu(&mut cpu) } {
        if r == 0 {
            return cpu as c_int;
        }
        Errno(-r).set();
        return -1;
    }
    // SAFETY: valid pointer.
    let r = unsafe { crate::arch::syscall3(309, &mut cpu as *mut c_uint as usize, 0, 0) };
    sys::check(r).map(|_| cpu as c_int).c_ret_or(-1)
}

/// `sched_get_priority_max(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn sched_get_priority_max(policy: c_int) -> c_int {
    // SAFETY: no memory is involved.
    sys::check(unsafe { crate::arch::syscall1(146, policy as usize) })
        .map(|v| v as c_int)
        .c_ret_or(-1)
}

/// `sched_get_priority_min(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn sched_get_priority_min(policy: c_int) -> c_int {
    // SAFETY: no memory is involved.
    sys::check(unsafe { crate::arch::syscall1(147, policy as usize) })
        .map(|v| v as c_int)
        .c_ret_or(-1)
}

/// `sched_getscheduler(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn sched_getscheduler(pid: c_int) -> c_int {
    // SAFETY: no memory is involved.
    sys::check(unsafe { crate::arch::syscall1(145, pid as usize) })
        .map(|v| v as c_int)
        .c_ret_or(-1)
}

/// `sched_setscheduler(2)`.
///
/// # Safety
/// `param` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sched_setscheduler(
    pid: c_int,
    policy: c_int,
    param: *const c_int,
) -> c_int {
    // SAFETY: caller contract.
    sys::check(unsafe { crate::arch::syscall3(144, pid as usize, policy as usize, param as usize) })
        .map(drop)
        .c_ret()
}

/// `sched_getparam(2)`.
///
/// # Safety
/// `param` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sched_getparam(pid: c_int, param: *mut c_int) -> c_int {
    // SAFETY: caller contract.
    sys::check(unsafe { crate::arch::syscall2(143, pid as usize, param as usize) })
        .map(drop)
        .c_ret()
}

/// `sched_setparam(2)`.
///
/// # Safety
/// `param` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sched_setparam(pid: c_int, param: *const c_int) -> c_int {
    // SAFETY: caller contract.
    sys::check(unsafe { crate::arch::syscall2(142, pid as usize, param as usize) })
        .map(drop)
        .c_ret()
}

/// `sched_rr_get_interval(2)`.
///
/// # Safety
/// `ts` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sched_rr_get_interval(pid: c_int, ts: *mut Timespec) -> c_int {
    // SAFETY: caller contract.
    sys::check(unsafe { crate::arch::syscall2(148, pid as usize, ts as usize) })
        .map(drop)
        .c_ret()
}

/// `sched_getaffinity(2)`: unlike the raw system call, returns 0 on
/// success and zero-fills the part of `mask` the kernel did not write.
///
/// # Safety
/// `mask` must be valid for `size` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn sched_getaffinity(pid: c_int, size: usize, mask: *mut c_void) -> c_int {
    // SAFETY: caller contract.
    let r = unsafe {
        crate::arch::syscall3(
            crate::arch::nr::SCHED_GETAFFINITY,
            pid as usize,
            size,
            mask as usize,
        )
    };
    match sys::check(r) {
        Ok(written) if written < size => {
            // SAFETY: `written <= size` and the buffer is `size` bytes.
            unsafe { ptr::write_bytes((mask as *mut u8).add(written), 0, size - written) };
            0
        }
        Ok(_) => 0,
        Err(e) => {
            e.set();
            -1
        }
    }
}

/// `CPU_COUNT` helper.
///
/// # Safety
/// `set` must be valid for `size` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn __sched_cpucount(size: usize, set: *const c_void) -> c_int {
    // SAFETY: caller contract.
    let bytes = unsafe { core::slice::from_raw_parts(set as *const u8, size) };
    bytes.iter().map(|b| b.count_ones() as c_int).sum()
}

// ---------------------------------------------------------------------
// timerfd / signalfd / inotify / shm / statfs / mlockall.

/// `timerfd_create(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn timerfd_create(clock: c_int, flags: c_int) -> c_int {
    // SAFETY: no memory is involved.
    sys::check(unsafe { crate::arch::syscall2(283, clock as usize, flags as usize) })
        .map(|v| v as c_int)
        .c_ret_or(-1)
}

/// `timerfd_settime(2)`.
///
/// # Safety
/// `new` must be valid; `old` null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn timerfd_settime(
    fd: c_int,
    flags: c_int,
    new: *const c_void,
    old: *mut c_void,
) -> c_int {
    // SAFETY: caller contract.
    sys::check(unsafe {
        crate::arch::syscall4(286, fd as usize, flags as usize, new as usize, old as usize)
    })
    .map(drop)
    .c_ret()
}

/// `timerfd_gettime(2)`.
///
/// # Safety
/// `cur` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn timerfd_gettime(fd: c_int, cur: *mut c_void) -> c_int {
    // SAFETY: caller contract.
    sys::check(unsafe { crate::arch::syscall2(287, fd as usize, cur as usize) })
        .map(drop)
        .c_ret()
}

/// `signalfd(2)`.
///
/// # Safety
/// `mask` must be a valid `sigset_t`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn signalfd(fd: c_int, mask: *const u64, flags: c_int) -> c_int {
    // SAFETY: caller contract; the kernel reads 8 bytes of the set.
    sys::check(unsafe { crate::arch::syscall4(289, fd as usize, mask as usize, 8, flags as usize) })
        .map(|v| v as c_int)
        .c_ret_or(-1)
}

/// `inotify_init1(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn inotify_init1(flags: c_int) -> c_int {
    // SAFETY: no memory is involved.
    sys::check(unsafe { crate::arch::syscall1(294, flags as usize) })
        .map(|v| v as c_int)
        .c_ret_or(-1)
}

/// `inotify_init(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn inotify_init() -> c_int {
    inotify_init1(0)
}

/// `inotify_add_watch(2)`.
///
/// # Safety
/// `path` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn inotify_add_watch(fd: c_int, path: *const c_char, mask: u32) -> c_int {
    // SAFETY: caller contract.
    sys::check(unsafe { crate::arch::syscall3(254, fd as usize, path as usize, mask as usize) })
        .map(|v| v as c_int)
        .c_ret_or(-1)
}

/// `inotify_rm_watch(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn inotify_rm_watch(fd: c_int, wd: c_int) -> c_int {
    // SAFETY: no memory is involved.
    sys::check(unsafe { crate::arch::syscall2(255, fd as usize, wd as usize) })
        .map(drop)
        .c_ret()
}

/// Builds `/dev/shm/<name>` for `shm_open`/`shm_unlink`.
///
/// # Safety
/// `name` must be NUL-terminated.
unsafe fn shm_path(name: *const c_char, buf: &mut [u8; 256 + 9]) -> Option<()> {
    // SAFETY: caller contract.
    let mut n = unsafe {
        core::slice::from_raw_parts(
            name as *const u8,
            crate::string::search::strlen(name as *const u8),
        )
    };
    while n.first() == Some(&b'/') {
        n = &n[1..];
    }
    if n.is_empty() || n.len() > 255 || n.contains(&b'/') || n == b"." || n == b".." {
        Errno::EINVAL.set();
        return None;
    }
    buf[..9].copy_from_slice(b"/dev/shm/");
    buf[9..9 + n.len()].copy_from_slice(n);
    buf[9 + n.len()] = 0;
    Some(())
}

/// `shm_open(3)`.
///
/// # Safety
/// `name` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn shm_open(name: *const c_char, flags: c_int, mode: c_uint) -> c_int {
    let mut path = [0u8; 265];
    // SAFETY: forwarded.
    if unsafe { shm_path(name, &mut path) }.is_none() {
        return -1;
    }
    // SAFETY: the path is NUL-terminated.
    unsafe {
        crate::fs::open(
            path.as_ptr() as *const c_char,
            flags | sys::O_NOFOLLOW | sys::O_CLOEXEC,
            mode,
        )
    }
}

/// `shm_unlink(3)`.
///
/// # Safety
/// `name` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn shm_unlink(name: *const c_char) -> c_int {
    let mut path = [0u8; 265];
    // SAFETY: forwarded.
    if unsafe { shm_path(name, &mut path) }.is_none() {
        return -1;
    }
    // SAFETY: the path is NUL-terminated.
    unsafe { crate::fs::unlink(path.as_ptr() as *const c_char) }
}

/// `statfs(2)`.
///
/// # Safety
/// `path` must be NUL-terminated; `buf` valid for `struct statfs`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn statfs(path: *const c_char, buf: *mut c_void) -> c_int {
    // SAFETY: caller contract.
    sys::check(unsafe {
        crate::arch::syscall2(crate::arch::nr::STATFS, path as usize, buf as usize)
    })
    .map(drop)
    .c_ret()
}

/// `fstatfs(2)`.
///
/// # Safety
/// `buf` must be valid for `struct statfs`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn fstatfs(fd: c_int, buf: *mut c_void) -> c_int {
    // SAFETY: caller contract.
    sys::check(unsafe {
        crate::arch::syscall2(crate::arch::nr::FSTATFS, fd as usize, buf as usize)
    })
    .map(drop)
    .c_ret()
}

/// `mlockall(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn mlockall(flags: c_int) -> c_int {
    // SAFETY: no memory is involved.
    sys::check(unsafe { crate::arch::syscall1(151, flags as usize) })
        .map(drop)
        .c_ret()
}

/// `munlockall(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn munlockall() -> c_int {
    // SAFETY: no memory is involved.
    sys::check(unsafe { crate::arch::syscall0(152) })
        .map(drop)
        .c_ret()
}

/// `utime(2)`.
///
/// # Safety
/// `path` must be NUL-terminated; `times` null or two `time_t`s.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn utime(path: *const c_char, times: *const i64) -> c_int {
    if times.is_null() {
        // SAFETY: forwarded.
        return unsafe { crate::fs::utimensat(sys::AT_FDCWD, path, ptr::null(), 0) };
    }
    // SAFETY: caller contract.
    let ts = unsafe {
        [
            Timespec {
                tv_sec: *times,
                tv_nsec: 0,
            },
            Timespec {
                tv_sec: *times.add(1),
                tv_nsec: 0,
            },
        ]
    };
    // SAFETY: forwarded.
    unsafe { crate::fs::utimensat(sys::AT_FDCWD, path, ts.as_ptr(), 0) }
}

/// `utimes(2)`.
///
/// # Safety
/// `path` must be NUL-terminated; `times` null or two `timeval`s.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn utimes(path: *const c_char, times: *const crate::time::Timeval) -> c_int {
    if times.is_null() {
        // SAFETY: forwarded.
        return unsafe { crate::fs::utimensat(sys::AT_FDCWD, path, ptr::null(), 0) };
    }
    // SAFETY: caller contract.
    let ts = unsafe {
        [
            Timespec {
                tv_sec: (*times).tv_sec,
                tv_nsec: (*times).tv_usec * 1000,
            },
            Timespec {
                tv_sec: (*times.add(1)).tv_sec,
                tv_nsec: (*times.add(1)).tv_usec * 1000,
            },
        ]
    };
    // SAFETY: forwarded.
    unsafe { crate::fs::utimensat(sys::AT_FDCWD, path, ts.as_ptr(), 0) }
}

/// Keeps the wide types referenced.
#[allow(dead_code)]
fn _types(_: c_ushort, _: c_ulong) {}

static TMPNAM_BUF: crate::sync::Mutex<[u8; 20]> = crate::sync::Mutex::new([0; 20]);

/// `tmpnam(3)`: a random name under `/tmp` that does not exist at the
/// time of the call (inherently racy; prefer `mkstemp`).
///
/// # Safety
/// `s` must be null or valid for `L_tmpnam` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn tmpnam(s: *mut c_char) -> *mut c_char {
    const ALPHABET: &[u8; 62] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
    let mut name = [0u8; 20];
    name[..9].copy_from_slice(b"/tmp/tmp.");
    for _ in 0..100 {
        let mut rnd = [0u8; 8];
        // SAFETY: valid buffer.
        if unsafe { crate::fs::getentropy(rnd.as_mut_ptr() as *mut c_void, rnd.len()) } != 0 {
            return ptr::null_mut();
        }
        for (i, r) in rnd.iter().enumerate() {
            name[9 + i] = ALPHABET[(*r % 62) as usize];
        }
        name[17] = 0;
        // SAFETY: NUL-terminated.
        if unsafe { crate::fs::access(name.as_ptr() as *const c_char, 0) } != 0 {
            let out = if s.is_null() {
                let mut g = TMPNAM_BUF.lock();
                *g = name;
                g.as_mut_ptr()
            } else {
                // SAFETY: caller contract.
                unsafe { ptr::copy_nonoverlapping(name.as_ptr(), s as *mut u8, 20) };
                s as *mut u8
            };
            return out as *mut c_char;
        }
    }
    ptr::null_mut()
}
