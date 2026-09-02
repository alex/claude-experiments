//! POSIX process and file descriptor primitives from `<unistd.h>`.

use crate::errno::{CReturn, CReturnOr, Errno};
use crate::sys;
use core::ffi::{c_int, c_uint, c_void};

/// `write(2)`.
///
/// # Safety
/// `buf` must be valid for reads of `count` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn write(fd: c_int, buf: *const c_void, count: usize) -> isize {
    crate::thread::cancel_point();
    // SAFETY: forwarded from the caller.
    let r = unsafe { sys::write(fd, buf as *const u8, count) };
    crate::thread::cancel_point();
    r.c_ret()
}

/// `read(2)`.
///
/// # Safety
/// `buf` must be valid for writes of `count` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn read(fd: c_int, buf: *mut c_void, count: usize) -> isize {
    crate::thread::cancel_point();
    // SAFETY: forwarded from the caller.
    let r = unsafe { sys::read(fd, buf as *mut u8, count) };
    crate::thread::cancel_point();
    r.c_ret()
}

/// `close(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn close(fd: c_int) -> c_int {
    sys::close(fd).c_ret()
}

/// `getpid(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn getpid() -> c_int {
    sys::getpid()
}

/// `gettid(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn gettid() -> c_int {
    sys::gettid()
}

/// `pread(2)`.
///
/// # Safety
/// `buf` must be valid for writes of `count` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pread(fd: c_int, buf: *mut c_void, count: usize, off: i64) -> isize {
    crate::thread::cancel_point();
    // SAFETY: forwarded from the caller.
    unsafe { sys::pread(fd, buf as *mut u8, count, off) }.c_ret()
}

/// `pwrite(2)`.
///
/// # Safety
/// `buf` must be valid for reads of `count` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pwrite(fd: c_int, buf: *const c_void, count: usize, off: i64) -> isize {
    crate::thread::cancel_point();
    // SAFETY: forwarded from the caller.
    unsafe { sys::pwrite(fd, buf as *const u8, count, off) }.c_ret()
}

/// `lseek(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn lseek(fd: c_int, off: i64, whence: c_int) -> i64 {
    match sys::lseek(fd, off, whence) {
        Ok(v) => v,
        Err(e) => {
            e.set();
            -1
        }
    }
}

/// `pipe2(2)`.
///
/// # Safety
/// `fds` must be valid for two ints.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pipe2(fds: *mut c_int, flags: c_int) -> c_int {
    // SAFETY: caller contract.
    let r = unsafe { crate::arch::syscall2(crate::arch::nr::PIPE2, fds as usize, flags as usize) };
    sys::check(r).map(drop).c_ret()
}

/// `pipe(2)`.
///
/// # Safety
/// `fds` must be valid for two ints.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn pipe(fds: *mut c_int) -> c_int {
    // SAFETY: forwarded.
    unsafe { pipe2(fds, 0) }
}

/// `dup(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn dup(fd: c_int) -> c_int {
    sys::dup(fd).c_ret()
}

/// `dup3(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn dup3(old: c_int, new: c_int, flags: c_int) -> c_int {
    // SAFETY: no memory is involved.
    let r = unsafe {
        crate::arch::syscall3(
            crate::arch::nr::DUP3,
            old as usize,
            new as usize,
            flags as usize,
        )
    };
    sys::check(r).map(|v| v as c_int).c_ret()
}

/// `dup2(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn dup2(old: c_int, new: c_int) -> c_int {
    if old == new {
        // `dup3` rejects this; `dup2` just checks that `old` is open.
        // SAFETY: F_GETFD takes no argument.
        return match unsafe { sys::fcntl(old, sys::F_GETFD, 0) } {
            Ok(_) => new,
            Err(e) => {
                e.set();
                -1
            }
        };
    }
    // SAFETY: no memory is involved.
    let r = unsafe { crate::arch::syscall3(crate::arch::nr::DUP3, old as usize, new as usize, 0) };
    sys::check(r).map(|v| v as c_int).c_ret()
}

/// `isatty(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn isatty(fd: c_int) -> c_int {
    let mut termios = [0u8; 64];
    // SAFETY: TCGETS writes a `struct termios` (60 bytes) into the buffer.
    match unsafe { sys::ioctl(fd, sys::TCGETS, termios.as_mut_ptr() as usize) } {
        Ok(_) => 1,
        Err(e) => {
            (if e == Errno::EINVAL { Errno::ENOTTY } else { e }).set();
            0
        }
    }
}

macro_rules! simple_syscalls {
    ($($(#[$doc:meta])* $name:ident($($arg:ident: $ty:ty),*) = $nr:ident -> $ret:ty, $fail:expr;)*) => {
        $(
            $(#[$doc])*
            #[cfg_attr(not(test), unsafe(no_mangle))]
            pub extern "C" fn $name($($arg: $ty),*) -> $ret {
                // SAFETY: no memory is involved.
                let r = unsafe { crate::arch::syscall_n(crate::arch::nr::$nr, &[$($arg as usize),*]) };
                sys::check(r).map(|v| v as $ret).c_ret_or($fail)
            }
        )*
    };
}

simple_syscalls! {
    /// `getppid(2)`.
    getppid() = GETPPID -> c_int, -1;
    /// `getuid(2)`.
    getuid() = GETUID -> c_uint, c_uint::MAX;
    /// `geteuid(2)`.
    geteuid() = GETEUID -> c_uint, c_uint::MAX;
    /// `getgid(2)`.
    getgid() = GETGID -> c_uint, c_uint::MAX;
    /// `getegid(2)`.
    getegid() = GETEGID -> c_uint, c_uint::MAX;
    /// `setuid(2)`.
    setuid(uid: c_uint) = SETUID -> c_int, -1;
    /// `setgid(2)`.
    setgid(gid: c_uint) = SETGID -> c_int, -1;
    /// `getpgid(2)`.
    getpgid(pid: c_int) = GETPGID -> c_int, -1;
    /// `setpgid(2)`.
    setpgid(pid: c_int, pgid: c_int) = SETPGID -> c_int, -1;
    /// `setsid(2)`.
    setsid() = SETSID -> c_int, -1;
    /// `getsid(2)`.
    getsid(pid: c_int) = GETSID -> c_int, -1;
}

/// `getpgrp(2)`: `getpgid(0)` (aarch64 has no `getpgrp` call).
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn getpgrp() -> c_int {
    getpgid(0)
}

/// `seteuid(2)`, via `setresuid`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn seteuid(uid: c_uint) -> c_int {
    // SAFETY: no memory is involved.
    let r = unsafe { crate::arch::syscall3(crate::arch::nr::SETRESUID, usize::MAX, uid as usize, usize::MAX) };
    sys::check(r).map(drop).c_ret()
}

/// `setegid(2)`, via `setresgid`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn setegid(gid: c_uint) -> c_int {
    // SAFETY: no memory is involved.
    let r = unsafe { crate::arch::syscall3(crate::arch::nr::SETRESGID, usize::MAX, gid as usize, usize::MAX) };
    sys::check(r).map(drop).c_ret()
}
