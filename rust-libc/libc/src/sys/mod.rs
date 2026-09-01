//! Typed wrappers over the raw system calls.
//!
//! Every syscall the library uses goes through this module, so it is the
//! single place to audit for kernel ABI usage. Functions return
//! [`Result`] with the kernel's negative return value converted into an
//! [`Errno`]; nothing here touches the C `errno` variable.

use crate::arch::{nr, syscall0, syscall1, syscall2, syscall3, syscall4, syscall5, syscall6};
use crate::errno::Errno;
use core::ffi::{c_int, c_void};
use core::sync::atomic::AtomicU32;

pub mod types;
pub use types::*;

/// The result of a system call.
pub type Result<T> = core::result::Result<T, Errno>;

/// Converts a raw kernel return value into a [`Result`].
///
/// The kernel returns `-errno` for failures; values in `[-4095, -1]` are
/// errors and everything else is a success (including large unsigned
/// values such as `mmap` addresses).
#[inline(always)]
pub fn check(ret: usize) -> Result<usize> {
    if ret > (-4096isize) as usize {
        Err(Errno((ret as isize).wrapping_neg() as i32))
    } else {
        Ok(ret)
    }
}

/// `read(2)`.
///
/// # Safety
/// `buf` must be valid for writes of `len` bytes.
pub unsafe fn read(fd: c_int, buf: *mut u8, len: usize) -> Result<usize> {
    // SAFETY: caller guarantees the buffer.
    unsafe { check(syscall3(nr::READ, fd as usize, buf as usize, len)) }
}

/// `write(2)`.
///
/// # Safety
/// `buf` must be valid for reads of `len` bytes.
pub unsafe fn write(fd: c_int, buf: *const u8, len: usize) -> Result<usize> {
    // SAFETY: caller guarantees the buffer.
    unsafe { check(syscall3(nr::WRITE, fd as usize, buf as usize, len)) }
}

/// `write(2)` of a whole slice, retrying on partial writes and `EINTR`.
pub fn write_all(fd: c_int, mut buf: &[u8]) -> Result<()> {
    while !buf.is_empty() {
        // SAFETY: the slice is valid for its length.
        match unsafe { write(fd, buf.as_ptr(), buf.len()) } {
            Ok(n) => buf = &buf[n..],
            Err(Errno::EINTR) => {}
            Err(e) => return Err(e),
        }
    }
    Ok(())
}

/// `close(2)`.
pub fn close(fd: c_int) -> Result<()> {
    // SAFETY: no memory is involved.
    unsafe { check(syscall1(nr::CLOSE, fd as usize)).map(drop) }
}

/// `exit_group(2)`: terminates every thread in the process.
pub fn exit_group(status: c_int) -> ! {
    // SAFETY: does not return.
    unsafe {
        syscall1(nr::EXIT_GROUP, status as usize);
    }
    crate::arch::trap()
}

/// `exit(2)`: terminates the calling thread only.
pub fn exit_thread(status: c_int) -> ! {
    // SAFETY: does not return.
    unsafe {
        syscall1(nr::EXIT, status as usize);
    }
    crate::arch::trap()
}

/// `getpid(2)`.
pub fn getpid() -> c_int {
    // SAFETY: cannot fail.
    unsafe { syscall0(nr::GETPID) as c_int }
}

/// `gettid(2)`.
pub fn gettid() -> c_int {
    // SAFETY: cannot fail.
    unsafe { syscall0(nr::GETTID) as c_int }
}

/// `kill(2)`.
pub fn kill(pid: c_int, sig: c_int) -> Result<()> {
    // SAFETY: no memory is involved.
    unsafe { check(syscall2(nr::KILL, pid as usize, sig as usize)).map(drop) }
}

/// `tgkill(2)`.
pub fn tgkill(tgid: c_int, tid: c_int, sig: c_int) -> Result<()> {
    // SAFETY: no memory is involved.
    unsafe {
        check(syscall3(
            nr::TGKILL,
            tgid as usize,
            tid as usize,
            sig as usize,
        ))
        .map(drop)
    }
}

/// `mmap(2)`.
///
/// # Safety
/// Mapping over existing memory (`MAP_FIXED`) is the caller's problem.
pub unsafe fn mmap(
    addr: *mut c_void,
    len: usize,
    prot: c_int,
    flags: c_int,
    fd: c_int,
    off: i64,
) -> Result<*mut u8> {
    // SAFETY: the kernel validates all arguments.
    let r = unsafe {
        syscall6(
            nr::MMAP,
            addr as usize,
            len,
            prot as usize,
            flags as usize,
            fd as usize,
            off as usize,
        )
    };
    check(r).map(|p| p as *mut u8)
}

/// `munmap(2)`.
///
/// # Safety
/// Nothing may reference the unmapped range afterwards.
pub unsafe fn munmap(addr: *mut u8, len: usize) -> Result<()> {
    // SAFETY: caller guarantees the range is no longer used.
    unsafe { check(syscall2(nr::MUNMAP, addr as usize, len)).map(drop) }
}

/// `mprotect(2)`.
///
/// # Safety
/// Changing protections of memory in use is the caller's problem.
pub unsafe fn mprotect(addr: *mut u8, len: usize, prot: c_int) -> Result<()> {
    // SAFETY: caller guarantees the range.
    unsafe { check(syscall3(nr::MPROTECT, addr as usize, len, prot as usize)).map(drop) }
}

/// `getrandom(2)`.
pub fn getrandom(buf: &mut [u8], flags: c_int) -> Result<usize> {
    // SAFETY: the slice is valid for writes of its length.
    unsafe {
        check(syscall3(
            nr::GETRANDOM,
            buf.as_mut_ptr() as usize,
            buf.len(),
            flags as usize,
        ))
    }
}

/// Fills `buf` completely with kernel randomness, retrying on `EINTR`.
pub fn getrandom_exact(mut buf: &mut [u8]) -> Result<()> {
    while !buf.is_empty() {
        match getrandom(buf, 0) {
            Ok(n) => buf = &mut buf[n..],
            Err(Errno::EINTR) => {}
            Err(e) => return Err(e),
        }
    }
    Ok(())
}

/// `futex(FUTEX_WAIT_PRIVATE)`: sleeps while `*addr == expected`.
///
/// Returns `Ok(())` when woken, or when the value already differed
/// (`EAGAIN`). Any timeout is relative.
pub fn futex_wait(addr: &AtomicU32, expected: u32, timeout: Option<&Timespec>) -> Result<()> {
    const FUTEX_WAIT_PRIVATE: usize = 128;
    let ts = timeout.map_or(core::ptr::null(), |t| t as *const Timespec);
    // SAFETY: `addr` and `ts` are valid for the duration of the call.
    let r = unsafe {
        syscall4(
            nr::FUTEX,
            addr.as_ptr() as usize,
            FUTEX_WAIT_PRIVATE,
            expected as usize,
            ts as usize,
        )
    };
    match check(r) {
        Ok(_) | Err(Errno::EAGAIN) => Ok(()),
        Err(e) => Err(e),
    }
}

/// `futex(FUTEX_WAKE_PRIVATE)`: wakes up to `n` waiters.
pub fn futex_wake(addr: &AtomicU32, n: c_int) -> Result<usize> {
    const FUTEX_WAKE_PRIVATE: usize = 1 | 128;
    // SAFETY: `addr` is valid.
    unsafe {
        check(syscall3(
            nr::FUTEX,
            addr.as_ptr() as usize,
            FUTEX_WAKE_PRIVATE,
            n as usize,
        ))
    }
}

/// `sched_yield(2)`.
pub fn sched_yield() {
    // SAFETY: cannot fail.
    unsafe {
        syscall0(nr::SCHED_YIELD);
    }
}

/// `rt_sigprocmask(2)` with the full 64-bit signal mask.
///
/// # Safety
/// `set` and `old` must each be null or valid.
pub unsafe fn rt_sigprocmask(how: c_int, set: *const u64, old: *mut u64) -> Result<()> {
    // SAFETY: caller guarantees the pointers.
    unsafe {
        check(syscall4(
            nr::RT_SIGPROCMASK,
            how as usize,
            set as usize,
            old as usize,
            8,
        ))
        .map(drop)
    }
}

/// `openat(2)`.
///
/// # Safety
/// `path` must be NUL-terminated.
pub unsafe fn openat(dirfd: c_int, path: *const u8, flags: c_int, mode: u32) -> Result<c_int> {
    // SAFETY: caller contract.
    unsafe {
        check(syscall4(
            nr::OPENAT,
            dirfd as usize,
            path as usize,
            flags as usize,
            mode as usize,
        ))
        .map(|fd| fd as c_int)
    }
}

/// `lseek(2)`.
pub fn lseek(fd: c_int, offset: i64, whence: c_int) -> Result<i64> {
    // SAFETY: no memory is involved.
    unsafe {
        check(syscall3(
            nr::LSEEK,
            fd as usize,
            offset as usize,
            whence as usize,
        ))
        .map(|v| v as i64)
    }
}

/// `ioctl(2)`.
///
/// # Safety
/// `arg` must be whatever the request expects.
pub unsafe fn ioctl(fd: c_int, request: usize, arg: usize) -> Result<c_int> {
    // SAFETY: caller contract.
    unsafe { check(syscall3(nr::IOCTL, fd as usize, request, arg)).map(|v| v as c_int) }
}

/// `unlinkat(2)`.
///
/// # Safety
/// `path` must be NUL-terminated.
pub unsafe fn unlinkat(dirfd: c_int, path: *const u8, flags: c_int) -> Result<()> {
    // SAFETY: caller contract.
    unsafe {
        check(syscall3(
            nr::UNLINKAT,
            dirfd as usize,
            path as usize,
            flags as usize,
        ))
        .map(drop)
    }
}

/// `renameat(2)`.
///
/// # Safety
/// Both paths must be NUL-terminated.
pub unsafe fn renameat(olddir: c_int, old: *const u8, newdir: c_int, new: *const u8) -> Result<()> {
    // SAFETY: caller contract.
    unsafe {
        check(syscall4(
            nr::RENAMEAT,
            olddir as usize,
            old as usize,
            newdir as usize,
            new as usize,
        ))
        .map(drop)
    }
}

/// `dup3(2)` / `dup(2)`: `dup3` with `flags = 0` and no `newfd` is not a
/// thing, so `dup` uses the plain syscall.
pub fn dup(fd: c_int) -> Result<c_int> {
    // SAFETY: no memory is involved.
    unsafe { check(syscall1(nr::DUP, fd as usize)).map(|v| v as c_int) }
}

/// `fcntl(2)`.
///
/// # Safety
/// `arg` must be whatever the command expects.
pub unsafe fn fcntl(fd: c_int, cmd: c_int, arg: usize) -> Result<c_int> {
    // SAFETY: caller contract.
    unsafe { check(syscall3(nr::FCNTL, fd as usize, cmd as usize, arg)).map(|v| v as c_int) }
}

/// `pread64(2)`.
///
/// # Safety
/// `buf` must be valid for writes of `len` bytes.
pub unsafe fn pread(fd: c_int, buf: *mut u8, len: usize, off: i64) -> Result<usize> {
    // SAFETY: caller contract.
    unsafe {
        check(syscall4(
            nr::PREAD64,
            fd as usize,
            buf as usize,
            len,
            off as usize,
        ))
    }
}

/// `pwrite64(2)`.
///
/// # Safety
/// `buf` must be valid for reads of `len` bytes.
pub unsafe fn pwrite(fd: c_int, buf: *const u8, len: usize, off: i64) -> Result<usize> {
    // SAFETY: caller contract.
    unsafe {
        check(syscall4(
            nr::PWRITE64,
            fd as usize,
            buf as usize,
            len,
            off as usize,
        ))
    }
}

/// Reserved so `syscall5` stays referenced until more wrappers use it.
#[allow(dead_code)]
fn _uses_syscall5() {
    let _ = syscall5 as unsafe fn(usize, usize, usize, usize, usize, usize) -> usize;
}

/// A [`core::fmt::Write`] implementation that writes directly to file
/// descriptor 2. Used for internal diagnostics only.
pub struct StderrWriter;

impl core::fmt::Write for StderrWriter {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        write_all(2, s.as_bytes()).map_err(|_| core::fmt::Error)
    }
}
