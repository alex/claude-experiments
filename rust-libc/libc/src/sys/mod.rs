//! Typed wrappers over the raw system calls.
//!
//! Every syscall the library uses goes through this module, so it is the
//! single place to audit for kernel ABI usage. Functions return
//! [`Result`] with the kernel's negative return value converted into an
//! [`Errno`]; nothing here touches the C `errno` variable.

use crate::arch::{nr, syscall0, syscall1, syscall2, syscall3, syscall4, syscall5, syscall6};
use crate::errno::Errno;
use core::ffi::{c_int, c_void};
use core::sync::atomic::{AtomicU32, AtomicUsize};

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
    match futex_wait_raw(addr, expected, timeout) {
        Ok(()) | Err(Errno::EAGAIN) => Ok(()),
        Err(e) => Err(e),
    }
}

/// [`futex_wait`] reporting the kernel's result as it is: `Ok(())` only
/// when actually woken by a `FUTEX_WAKE` (or a requeue followed by one),
/// `Err(EAGAIN)` when the value already differed, `Err(EINTR)` for a
/// signal.
pub fn futex_wait_raw(addr: &AtomicU32, expected: u32, timeout: Option<&Timespec>) -> Result<()> {
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
    check(r).map(|_| ())
}

/// `futex(FUTEX_WAIT)` with a *shared* key. Needed to wait for the tid
/// word cleared by `CLONE_CHILD_CLEARTID`: the kernel wakes it with a
/// shared key, which never matches a `FUTEX_PRIVATE` waiter.
pub fn futex_wait_shared(addr: &AtomicU32, expected: u32) -> Result<()> {
    const FUTEX_WAIT: usize = 0;
    // SAFETY: `addr` is valid for the duration of the call.
    let r = unsafe {
        syscall4(
            nr::FUTEX,
            addr.as_ptr() as usize,
            FUTEX_WAIT,
            expected as usize,
            0,
        )
    };
    match check(r) {
        Ok(_) | Err(Errno::EAGAIN) => Ok(()),
        Err(e) => Err(e),
    }
}

/// `futex(FUTEX_WAIT_BITSET_PRIVATE)` with an *absolute* timeout on
/// `clock` (`CLOCK_REALTIME` or `CLOCK_MONOTONIC`). Returns
/// `Err(ETIMEDOUT)` on timeout; a value mismatch counts as woken.
pub fn futex_wait_abs(
    addr: &AtomicU32,
    expected: u32,
    deadline: &Timespec,
    clock: c_int,
) -> Result<()> {
    const FUTEX_WAIT_BITSET_PRIVATE: usize = 9 | 128;
    const FUTEX_CLOCK_REALTIME: usize = 256;
    const FUTEX_BITSET_MATCH_ANY: usize = 0xffff_ffff;
    let op = FUTEX_WAIT_BITSET_PRIVATE
        | if clock == CLOCK_REALTIME {
            FUTEX_CLOCK_REALTIME
        } else {
            0
        };
    // SAFETY: `addr` and `deadline` are valid for the call.
    let r = unsafe {
        syscall6(
            nr::FUTEX,
            addr.as_ptr() as usize,
            op,
            expected as usize,
            deadline as *const Timespec as usize,
            0,
            FUTEX_BITSET_MATCH_ANY,
        )
    };
    match check(r) {
        Ok(_) | Err(Errno::EAGAIN) => Ok(()),
        Err(e) => Err(e),
    }
}

/// `clock_gettime(2)`.
pub fn clock_gettime(clock: c_int) -> Result<Timespec> {
    let mut ts = Timespec::default();
    // The vDSO answers without entering the kernel when it can.
    // SAFETY: `ts` is a valid local.
    if let Some(r) = unsafe { crate::vdso::clock_gettime(clock, &mut ts) } {
        return if r == 0 { Ok(ts) } else { Err(Errno(-r)) };
    }
    // SAFETY: `ts` is valid for the write.
    unsafe {
        check(syscall2(
            nr::CLOCK_GETTIME,
            clock as usize,
            &mut ts as *mut Timespec as usize,
        ))?
    };
    Ok(ts)
}

/// `futex(FUTEX_WAKE_PRIVATE)`: wakes up to `n` waiters.
/// `futex(FUTEX_WAKE_PRIVATE)`: wakes up to `n` waiters.
/// `futex(FUTEX_CMP_REQUEUE_PRIVATE)`: if `*addr == expected`, wakes
/// `wake` waiters of `addr` and moves up to `requeue` more to wait on
/// `target` instead. Fails with `EAGAIN` if the value changed.
pub fn futex_cmp_requeue(
    addr: &AtomicU32,
    expected: u32,
    wake: c_int,
    requeue: c_int,
    target: &AtomicU32,
) -> Result<usize> {
    const FUTEX_CMP_REQUEUE_PRIVATE: usize = 4 | 128;
    // SAFETY: both words are valid.
    unsafe {
        check(syscall6(
            nr::FUTEX,
            addr.as_ptr() as usize,
            FUTEX_CMP_REQUEUE_PRIVATE,
            wake as usize,
            requeue as usize,
            target.as_ptr() as usize,
            expected as usize,
        ))
    }
}

/// `futex(FUTEX_WAKE_PRIVATE)`: wakes up to `n` waiters of `addr`.
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

/// The kernel's page size, from `AT_PAGESZ` (aarch64 kernels may use
/// 16 or 64 KiB pages). Anything the kernel requires to be page aligned
/// (`mprotect`, `madvise`, guard pages) must use this.
static PAGE_SIZE: AtomicUsize = AtomicUsize::new(MIN_PAGE_SIZE);

/// The page size of the running kernel.
#[inline]
pub fn page_size() -> usize {
    PAGE_SIZE.load(core::sync::atomic::Ordering::Relaxed)
}

/// Records the page size reported by the kernel (startup only).
pub fn set_page_size(size: usize) {
    if size.is_power_of_two() && size >= MIN_PAGE_SIZE {
        PAGE_SIZE.store(size, core::sync::atomic::Ordering::Relaxed);
    }
}

/// `renameat(2)`.
///
/// # Safety
/// Both paths must be NUL-terminated.
pub unsafe fn renameat(olddir: c_int, old: *const u8, newdir: c_int, new: *const u8) -> Result<()> {
    // SAFETY: caller contract.
    unsafe {
        // `renameat2` with no flags: the only form every architecture has.
        check(syscall5(
            nr::RENAMEAT2,
            olddir as usize,
            old as usize,
            newdir as usize,
            new as usize,
            0,
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

/// `rt_sigaction(2)` with the kernel's `struct sigaction` layout.
///
/// # Safety
/// `new` and `old` must be null or valid.
pub unsafe fn rt_sigaction(
    sig: c_int,
    new: *const KernelSigaction,
    old: *mut KernelSigaction,
) -> Result<()> {
    // SAFETY: caller contract.
    unsafe {
        check(syscall4(
            nr::RT_SIGACTION,
            sig as usize,
            new as usize,
            old as usize,
            8,
        ))
        .map(drop)
    }
}

/// `fork(2)`. Returns the child's pid in the parent and 0 in the child.
pub fn fork() -> Result<c_int> {
    // `clone(SIGCHLD)` is what `fork` is on every architecture (some have
    // no `fork` system call); with every other argument zero the argument
    // order differences do not matter.
    // SAFETY: no memory is involved.
    unsafe { check(syscall5(nr::CLONE, SIGCHLD as usize, 0, 0, 0, 0)).map(|v| v as c_int) }
}

/// `execve(2)`.
///
/// # Safety
/// All pointers must be valid NUL-terminated strings / NULL-terminated
/// arrays.
pub unsafe fn execve(path: *const u8, argv: *const *const u8, envp: *const *const u8) -> Errno {
    // SAFETY: caller contract.
    let r = unsafe { syscall3(nr::EXECVE, path as usize, argv as usize, envp as usize) };
    check(r).err().unwrap_or(Errno::EINVAL)
}

/// `wait4(2)`.
///
/// # Safety
/// `status` and `rusage` must be null or valid.
pub unsafe fn wait4(
    pid: c_int,
    status: *mut c_int,
    options: c_int,
    rusage: *mut c_void,
) -> Result<c_int> {
    // SAFETY: caller contract.
    unsafe {
        check(syscall4(
            nr::WAIT4,
            pid as usize,
            status as usize,
            options as usize,
            rusage as usize,
        ))
        .map(|v| v as c_int)
    }
}

/// A [`core::fmt::Write`] implementation that writes directly to file
/// descriptor 2. Used for internal diagnostics only.
pub struct StderrWriter;

impl core::fmt::Write for StderrWriter {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        write_all(2, s.as_bytes()).map_err(|_| core::fmt::Error)
    }
}
