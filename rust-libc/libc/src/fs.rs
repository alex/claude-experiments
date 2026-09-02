//! File system and system calls from `<fcntl.h>`, `<sys/stat.h>`,
//! `<unistd.h>`, `<sys/mman.h>`, `<sys/uio.h>`, `<sys/utsname.h>`,
//! `<sys/resource.h>` and friends.
//!
//! Variadic functions whose extra argument is an integer (`open`,
//! `fcntl`, `ioctl`, `prctl`, `syscall`) are declared with a fixed
//! parameter list: on x86_64 (and AArch64 Linux) variadic integer
//! arguments travel in exactly the registers fixed ones would, so the
//! implementation can read the "optional" argument directly. The value is
//! only used when the flags say the caller supplied it.

use crate::c_char;
use crate::errno::{CReturn, CReturnOr, Errno};
use crate::malloc;
use crate::sys::{self, AT_FDCWD, Timespec};
use core::ffi::{c_int, c_long, c_uint, c_ulong, c_void};
use core::ptr;

/// `struct stat` (x86_64 kernel layout, 144 bytes).
#[allow(missing_docs)]
#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
#[cfg(target_arch = "x86_64")]
pub struct Stat {
    pub st_dev: u64,
    pub st_ino: u64,
    pub st_nlink: u64,
    pub st_mode: u32,
    pub st_uid: u32,
    pub st_gid: u32,
    pub _pad0: u32,
    pub st_rdev: u64,
    pub st_size: i64,
    pub st_blksize: i64,
    pub st_blocks: i64,
    pub st_atim: Timespec,
    pub st_mtim: Timespec,
    pub st_ctim: Timespec,
    pub _unused: [i64; 3],
}

/// `struct stat` (the asm-generic layout used by aarch64).
#[allow(missing_docs)]
#[repr(C)]
#[derive(Clone, Copy, Default)]
#[cfg(target_arch = "aarch64")]
pub struct Stat {
    pub st_dev: u64,
    pub st_ino: u64,
    pub st_mode: u32,
    pub st_nlink: u32,
    pub st_uid: u32,
    pub st_gid: u32,
    pub st_rdev: u64,
    pub _pad1: u64,
    pub st_size: i64,
    pub st_blksize: i32,
    pub _pad2: i32,
    pub st_blocks: i64,
    pub st_atim: Timespec,
    pub st_mtim: Timespec,
    pub st_ctim: Timespec,
    pub _unused: [u32; 2],
}

#[cfg(target_arch = "x86_64")]
const _: () = assert!(core::mem::size_of::<Stat>() == 144);
#[cfg(target_arch = "aarch64")]
const _: () = assert!(core::mem::size_of::<Stat>() == 128);

/// `AT_SYMLINK_NOFOLLOW`.
pub const AT_SYMLINK_NOFOLLOW: c_int = 0x100;
/// `AT_EMPTY_PATH`.
pub const AT_EMPTY_PATH: c_int = 0x1000;

macro_rules! syscalls {
    ($($(#[$doc:meta])* $vis:vis unsafe fn $name:ident($($arg:ident: $ty:ty),*) = $nr:expr => $ret:ty, $fail:expr;)*) => {
        $(
            $(#[$doc])*
            ///
            /// # Safety
            /// Pointer arguments must be valid for what the kernel does with them.
            #[cfg_attr(not(test), unsafe(no_mangle))]
            $vis unsafe extern "C" fn $name($($arg: $ty),*) -> $ret {
                // SAFETY: caller contract.
                let r = unsafe { crate::arch::syscall_n($nr, &[$($arg as usize),*]) };
                sys::check(r).map(|v| v as $ret).c_ret_or($fail)
            }
        )*
    };
}

/// Like [`syscalls!`] for calls that take only integers: nothing about
/// them can violate memory safety, so they are safe functions.
macro_rules! safe_syscalls {
    ($($(#[$doc:meta])* $vis:vis fn $name:ident($($arg:ident: $ty:ty),*) = $nr:expr => $ret:ty, $fail:expr;)*) => {
        $(
            $(#[$doc])*
            #[cfg_attr(not(test), unsafe(no_mangle))]
            $vis extern "C" fn $name($($arg: $ty),*) -> $ret {
                // SAFETY: no memory is involved.
                let r = unsafe { crate::arch::syscall_n($nr, &[$($arg as usize),*]) };
                sys::check(r).map(|v| v as $ret).c_ret_or($fail)
            }
        )*
    };
}

use crate::arch::nr;

syscalls! {
    /// `openat(2)`; `mode` is read only with `O_CREAT`/`O_TMPFILE`.
    pub unsafe fn openat(dirfd: c_int, path: *const c_char, flags: c_int, mode: c_uint) = nr::OPENAT => c_int, -1;
    /// `fcntl(2)`.
    pub unsafe fn fcntl(fd: c_int, cmd: c_int, arg: c_ulong) = nr::FCNTL => c_int, -1;
    /// `ioctl(2)`.
    pub unsafe fn ioctl(fd: c_int, request: c_ulong, arg: c_ulong) = nr::IOCTL => c_int, -1;
    /// `fstatat(2)` (`newfstatat`).
    pub unsafe fn fstatat(dirfd: c_int, path: *const c_char, st: *mut Stat, flags: c_int) = nr::NEWFSTATAT => c_int, -1;
    /// `fstat(2)`.
    pub unsafe fn fstat(fd: c_int, st: *mut Stat) = nr::FSTAT => c_int, -1;
    /// `chdir(2)`.
    pub unsafe fn chdir(path: *const c_char) = nr::CHDIR => c_int, -1;
    /// `mkdirat(2)`.
    pub unsafe fn mkdirat(dirfd: c_int, path: *const c_char, mode: c_uint) = nr::MKDIRAT => c_int, -1;
    /// `unlinkat(2)`.
    pub unsafe fn unlinkat(dirfd: c_int, path: *const c_char, flags: c_int) = nr::UNLINKAT => c_int, -1;
    /// `linkat(2)`.
    pub unsafe fn linkat(olddir: c_int, old: *const c_char, newdir: c_int, new: *const c_char, flags: c_int) = nr::LINKAT => c_int, -1;
    /// `symlinkat(2)`.
    pub unsafe fn symlinkat(target: *const c_char, dirfd: c_int, path: *const c_char) = nr::SYMLINKAT => c_int, -1;
    /// `readlinkat(2)`.
    pub unsafe fn readlinkat(dirfd: c_int, path: *const c_char, buf: *mut c_char, len: usize) = nr::READLINKAT => isize, -1;
    /// `renameat2(2)`.
    pub unsafe fn renameat2(olddir: c_int, old: *const c_char, newdir: c_int, new: *const c_char, flags: c_uint) = nr::RENAMEAT2 => c_int, -1;
    /// `fchmodat(2)`.
    pub unsafe fn fchmodat(dirfd: c_int, path: *const c_char, mode: c_uint, flags: c_int) = nr::FCHMODAT => c_int, -1;
    /// `fchownat(2)`.
    pub unsafe fn fchownat(dirfd: c_int, path: *const c_char, uid: c_uint, gid: c_uint, flags: c_int) = nr::FCHOWNAT => c_int, -1;
    /// `truncate(2)`.
    pub unsafe fn truncate(path: *const c_char, len: i64) = nr::TRUNCATE => c_int, -1;
    /// `utimensat(2)`.
    pub unsafe fn utimensat(dirfd: c_int, path: *const c_char, times: *const Timespec, flags: c_int) = nr::UTIMENSAT => c_int, -1;
    /// `readv(2)`.
    pub unsafe fn readv(fd: c_int, iov: *const c_void, count: c_int) = nr::READV => isize, -1;
    /// `writev(2)`.
    pub unsafe fn writev(fd: c_int, iov: *const c_void, count: c_int) = nr::WRITEV => isize, -1;
    /// `preadv(2)`.
    pub unsafe fn preadv(fd: c_int, iov: *const c_void, count: c_int, off: i64) = nr::PREADV => isize, -1;
    /// `pwritev(2)`.
    pub unsafe fn pwritev(fd: c_int, iov: *const c_void, count: c_int, off: i64) = nr::PWRITEV => isize, -1;
    /// `sendfile(2)`.
    pub unsafe fn sendfile(out_fd: c_int, in_fd: c_int, off: *mut i64, count: usize) = nr::SENDFILE => isize, -1;
    /// `munmap(2)`.
    pub unsafe fn munmap(addr: *mut c_void, len: usize) = nr::MUNMAP => c_int, -1;
    /// `mprotect(2)`.
    pub unsafe fn mprotect(addr: *mut c_void, len: usize, prot: c_int) = nr::MPROTECT => c_int, -1;
    /// `madvise(2)`.
    pub unsafe fn madvise(addr: *mut c_void, len: usize, advice: c_int) = nr::MADVISE => c_int, -1;
    /// `msync(2)`.
    pub unsafe fn msync(addr: *mut c_void, len: usize, flags: c_int) = nr::MSYNC => c_int, -1;
    /// `mlock(2)`.
    pub unsafe fn mlock(addr: *const c_void, len: usize) = nr::MLOCK => c_int, -1;
    /// `munlock(2)`.
    pub unsafe fn munlock(addr: *const c_void, len: usize) = nr::MUNLOCK => c_int, -1;
    /// `chroot(2)`.
    pub unsafe fn chroot(path: *const c_char) = nr::CHROOT => c_int, -1;
    /// `prctl(2)`.
    pub unsafe fn prctl(option: c_int, a2: c_ulong, a3: c_ulong, a4: c_ulong, a5: c_ulong) = nr::PRCTL => c_int, -1;
    /// `getrusage(2)`.
    pub unsafe fn getrusage(who: c_int, usage: *mut c_void) = nr::GETRUSAGE => c_int, -1;
    /// `uname(2)`.
    pub unsafe fn uname(buf: *mut c_void) = nr::UNAME => c_int, -1;
    /// `mknodat(2)`.
    pub unsafe fn mknodat(dirfd: c_int, path: *const c_char, mode: c_uint, dev: c_ulong) = nr::MKNODAT => c_int, -1;
    /// `sched_setaffinity(2)`.
    pub unsafe fn sched_setaffinity(pid: c_int, size: usize, mask: *const c_void) = nr::SCHED_SETAFFINITY => c_int, -1;
    /// `sysinfo(2)`.
    pub unsafe fn sysinfo(info: *mut c_void) = nr::SYSINFO => c_int, -1;
    /// `memfd_create(2)`.
    pub unsafe fn memfd_create(name: *const c_char, flags: c_uint) = nr::MEMFD_CREATE => c_int, -1;
    /// `statx(2)`.
    pub unsafe fn statx(dirfd: c_int, path: *const c_char, flags: c_int, mask: c_uint, buf: *mut c_void) = nr::STATX => c_int, -1;
    /// `getpriority(2)`; the kernel returns `20 - nice`, see wrapper.
    unsafe fn getpriority_raw(which: c_int, who: c_int) = nr::GETPRIORITY => c_int, -1;
    /// `setrlimit` via `prlimit64` on the calling process.
    unsafe fn prlimit64(pid: c_int, resource: c_int, new: *const c_void, old: *mut c_void) = nr::PRLIMIT64 => c_int, -1;
    /// `times(2)`.
    pub unsafe fn times(buf: *mut c_void) = nr::TIMES => c_long, -1;
    /// `getitimer(2)`.
    pub unsafe fn getitimer(which: c_int, value: *mut c_void) = nr::GETITIMER => c_int, -1;
    /// `setitimer(2)`.
    pub unsafe fn setitimer(which: c_int, new: *const c_void, old: *mut c_void) = nr::SETITIMER => c_int, -1;
}

safe_syscalls! {
    /// `fchdir(2)`.
    pub fn fchdir(fd: c_int) = nr::FCHDIR => c_int, -1;
    /// `fchmod(2)`.
    pub fn fchmod(fd: c_int, mode: c_uint) = nr::FCHMOD => c_int, -1;
    /// `fchown(2)`.
    pub fn fchown(fd: c_int, uid: c_uint, gid: c_uint) = nr::FCHOWN => c_int, -1;
    /// `umask(2)`.
    pub fn umask(mask: c_uint) = nr::UMASK => c_uint, 0;
    /// `ftruncate(2)`.
    pub fn ftruncate(fd: c_int, len: i64) = nr::FTRUNCATE => c_int, -1;
    /// `fsync(2)`.
    pub fn fsync(fd: c_int) = nr::FSYNC => c_int, -1;
    /// `fdatasync(2)`.
    pub fn fdatasync(fd: c_int) = nr::FDATASYNC => c_int, -1;
    /// `flock(2)`.
    pub fn flock(fd: c_int, op: c_int) = nr::FLOCK => c_int, -1;
    /// `sync(2)`.
    pub fn sync() = nr::SYNC => c_int, -1;
    /// `setpriority(2)`.
    pub fn setpriority(which: c_int, who: c_int, prio: c_int) = nr::SETPRIORITY => c_int, -1;
    /// `eventfd2(2)`.
    pub fn eventfd(initval: c_uint, flags: c_int) = nr::EVENTFD2 => c_int, -1;
}

/// `open(2)`.
///
/// # Safety
/// `path` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn open(path: *const c_char, flags: c_int, mode: c_uint) -> c_int {
    crate::thread::cancel_point();
    // SAFETY: forwarded.
    unsafe { openat(AT_FDCWD, path, flags, mode) }
}

/// `creat(2)`.
///
/// # Safety
/// `path` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn creat(path: *const c_char, mode: c_uint) -> c_int {
    // SAFETY: forwarded.
    unsafe {
        openat(
            AT_FDCWD,
            path,
            sys::O_WRONLY | sys::O_CREAT | sys::O_TRUNC,
            mode,
        )
    }
}

/// `stat(2)`.
///
/// # Safety
/// `path` must be NUL-terminated; `st` valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn stat(path: *const c_char, st: *mut Stat) -> c_int {
    // SAFETY: forwarded.
    unsafe { fstatat(AT_FDCWD, path, st, 0) }
}

/// `lstat(2)`.
///
/// # Safety
/// `path` must be NUL-terminated; `st` valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn lstat(path: *const c_char, st: *mut Stat) -> c_int {
    // SAFETY: forwarded.
    unsafe { fstatat(AT_FDCWD, path, st, AT_SYMLINK_NOFOLLOW) }
}

/// `access(2)`.
///
/// # Safety
/// `path` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn access(path: *const c_char, mode: c_int) -> c_int {
    // SAFETY: forwarded.
    unsafe { faccessat(AT_FDCWD, path, mode, 0) }
}

/// `faccessat(2)`: `faccessat2` where the kernel has it, else the
/// original call (which takes no flags).
///
/// # Safety
/// `path` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn faccessat(
    dirfd: c_int,
    path: *const c_char,
    mode: c_int,
    flags: c_int,
) -> c_int {
    let args = [dirfd as usize, path as usize, mode as usize, flags as usize];
    // SAFETY: caller contract.
    let mut r = unsafe { crate::arch::syscall_n(nr::FACCESSAT2, &args) };
    if sys::check(r) == Err(Errno::ENOSYS) && flags == 0 {
        // SAFETY: as above.
        r = unsafe { crate::arch::syscall_n(nr::FACCESSAT, &args[..3]) };
    }
    sys::check(r).map(|v| v as c_int).c_ret_or(-1)
}

/// `renameat(2)`: `renameat2` without flags, the form every
/// architecture has.
///
/// # Safety
/// Both paths must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn renameat(
    olddir: c_int,
    old: *const c_char,
    newdir: c_int,
    new: *const c_char,
) -> c_int {
    // SAFETY: forwarded.
    unsafe { renameat2(olddir, old, newdir, new, 0) }
}

/// `mkdir(2)`.
///
/// # Safety
/// `path` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mkdir(path: *const c_char, mode: c_uint) -> c_int {
    // SAFETY: forwarded.
    unsafe { mkdirat(AT_FDCWD, path, mode) }
}

/// `rmdir(2)`.
///
/// # Safety
/// `path` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn rmdir(path: *const c_char) -> c_int {
    // SAFETY: forwarded.
    unsafe { unlinkat(AT_FDCWD, path, sys::AT_REMOVEDIR) }
}

/// `unlink(2)`.
///
/// # Safety
/// `path` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn unlink(path: *const c_char) -> c_int {
    // SAFETY: forwarded.
    unsafe { unlinkat(AT_FDCWD, path, 0) }
}

/// `link(2)`.
///
/// # Safety
/// Both paths must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn link(old: *const c_char, new: *const c_char) -> c_int {
    // SAFETY: forwarded.
    unsafe { linkat(AT_FDCWD, old, AT_FDCWD, new, 0) }
}

/// `symlink(2)`.
///
/// # Safety
/// Both paths must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn symlink(target: *const c_char, path: *const c_char) -> c_int {
    // SAFETY: forwarded.
    unsafe { symlinkat(target, AT_FDCWD, path) }
}

/// `readlink(2)`.
///
/// # Safety
/// `path` must be NUL-terminated; `buf` valid for `len` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn readlink(path: *const c_char, buf: *mut c_char, len: usize) -> isize {
    // SAFETY: forwarded.
    unsafe { readlinkat(AT_FDCWD, path, buf, len) }
}

/// `chmod(2)`.
///
/// # Safety
/// `path` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn chmod(path: *const c_char, mode: c_uint) -> c_int {
    // SAFETY: forwarded.
    unsafe { fchmodat(AT_FDCWD, path, mode, 0) }
}

/// `chown(2)`.
///
/// # Safety
/// `path` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn chown(path: *const c_char, uid: c_uint, gid: c_uint) -> c_int {
    // SAFETY: forwarded.
    unsafe { fchownat(AT_FDCWD, path, uid, gid, 0) }
}

/// `lchown(2)`.
///
/// # Safety
/// `path` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn lchown(path: *const c_char, uid: c_uint, gid: c_uint) -> c_int {
    // SAFETY: forwarded.
    unsafe { fchownat(AT_FDCWD, path, uid, gid, AT_SYMLINK_NOFOLLOW) }
}

/// `mknod(2)`.
///
/// # Safety
/// `path` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mknod(path: *const c_char, mode: c_uint, dev: c_ulong) -> c_int {
    // SAFETY: forwarded.
    unsafe { mknodat(AT_FDCWD, path, mode, dev) }
}

/// `mkfifo(3)`.
///
/// # Safety
/// `path` must be NUL-terminated.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mkfifo(path: *const c_char, mode: c_uint) -> c_int {
    // SAFETY: forwarded.
    unsafe { mknodat(AT_FDCWD, path, mode | 0o10000, 0) }
}

/// `futimens(3)`.
///
/// # Safety
/// `times` must be null or point to two timespecs.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn futimens(fd: c_int, times: *const Timespec) -> c_int {
    // SAFETY: forwarded; a null path with a plain fd is what the kernel expects.
    unsafe { utimensat(fd, ptr::null(), times, 0) }
}

/// `getcwd(3)`. With a NULL buffer the result is `malloc`ed.
///
/// # Safety
/// `buf` must be null or valid for `size` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getcwd(buf: *mut c_char, size: usize) -> *mut c_char {
    if buf.is_null() {
        let mut tmp = [0u8; 4096];
        // SAFETY: the buffer is valid.
        let r = unsafe { crate::arch::syscall2(nr::GETCWD, tmp.as_mut_ptr() as usize, tmp.len()) };
        let n = match sys::check(r) {
            Ok(n) => n,
            Err(e) => {
                e.set();
                return ptr::null_mut();
            }
        };
        if size != 0 && n > size {
            Errno::ERANGE.set();
            return ptr::null_mut();
        }
        let out = malloc::alloc(n.max(size)) as *mut c_char;
        if out.is_null() {
            return out;
        }
        // SAFETY: the block holds `n` bytes.
        unsafe { ptr::copy_nonoverlapping(tmp.as_ptr(), out as *mut u8, n) };
        return out;
    }
    if size == 0 {
        Errno::EINVAL.set();
        return ptr::null_mut();
    }
    // SAFETY: caller contract.
    let r = unsafe { crate::arch::syscall2(nr::GETCWD, buf as usize, size) };
    match sys::check(r) {
        Ok(_) => buf,
        Err(e) => {
            e.set();
            ptr::null_mut()
        }
    }
}

/// `mmap(2)`.
///
/// # Safety
/// As for the system call.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mmap(
    addr: *mut c_void,
    len: usize,
    prot: c_int,
    flags: c_int,
    fd: c_int,
    off: i64,
) -> *mut c_void {
    if off % sys::page_size() as i64 != 0 || len == 0 {
        Errno::EINVAL.set();
        return usize::MAX as *mut c_void;
    }
    // SAFETY: forwarded.
    match unsafe { sys::mmap(addr, len, prot, flags, fd, off) } {
        Ok(p) => p as *mut c_void,
        Err(e) => {
            e.set();
            usize::MAX as *mut c_void
        }
    }
}

/// `mremap(2)`.
///
/// # Safety
/// As for the system call.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mremap(
    old: *mut c_void,
    old_len: usize,
    new_len: usize,
    flags: c_int,
    new_addr: *mut c_void,
) -> *mut c_void {
    // SAFETY: forwarded.
    let r = unsafe {
        crate::arch::syscall5(
            nr::MREMAP,
            old as usize,
            old_len,
            new_len,
            flags as usize,
            new_addr as usize,
        )
    };
    match sys::check(r) {
        Ok(p) => p as *mut c_void,
        Err(e) => {
            e.set();
            usize::MAX as *mut c_void
        }
    }
}

/// `getpriority(2)`: converts the kernel's `20 - nice` encoding.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn getpriority(which: c_int, who: c_int) -> c_int {
    // SAFETY: no memory is involved.
    let r = unsafe { getpriority_raw(which, who) };
    if r < 0 { r } else { 20 - r }
}

/// `nice(2)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn nice(inc: c_int) -> c_int {
    let cur = getpriority(0, 0);
    let new = cur.saturating_add(inc).clamp(-20, 19);
    if setpriority(0, 0, new) < 0 {
        -1
    } else {
        new
    }
}

/// `struct rlimit`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Rlimit {
    /// Soft limit.
    pub rlim_cur: u64,
    /// Hard limit.
    pub rlim_max: u64,
}

/// `getrlimit(2)`.
///
/// # Safety
/// `out` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getrlimit(resource: c_int, out: *mut Rlimit) -> c_int {
    // SAFETY: forwarded.
    unsafe { prlimit64(0, resource, ptr::null(), out as *mut c_void) }
}

/// `setrlimit(2)`.
///
/// # Safety
/// `new` must be valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn setrlimit(resource: c_int, new: *const Rlimit) -> c_int {
    // SAFETY: forwarded.
    unsafe { prlimit64(0, resource, new as *const c_void, ptr::null_mut()) }
}

/// `prlimit(2)`.
///
/// # Safety
/// Both pointers must be null or valid.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn prlimit(
    pid: c_int,
    resource: c_int,
    new: *const Rlimit,
    old: *mut Rlimit,
) -> c_int {
    // SAFETY: forwarded.
    unsafe { prlimit64(pid, resource, new as *const c_void, old as *mut c_void) }
}

/// `getpagesize(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn getpagesize() -> c_int {
    sys::page_size() as c_int
}

/// Number of online CPUs, from the affinity mask.
fn cpu_count() -> c_long {
    let mut mask = [0u64; 16];
    // SAFETY: the buffer is 128 bytes.
    let r = unsafe { crate::extra::sched_getaffinity(0, 128, mask.as_mut_ptr() as *mut c_void) };
    if r < 0 {
        return 1;
    }
    mask.iter()
        .map(|w| w.count_ones() as c_long)
        .sum::<c_long>()
        .max(1)
}

/// `struct sysinfo` (only the fields we read).
#[repr(C)]
struct SysInfo {
    uptime: i64,
    loads: [u64; 3],
    totalram: u64,
    freeram: u64,
    rest: [u8; 112 - 48],
}

/// `sysconf(3)` for the commonly used names.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn sysconf(name: c_int) -> c_long {
    const SC_ARG_MAX: c_int = 0;
    const SC_CHILD_MAX: c_int = 1;
    const SC_CLK_TCK: c_int = 2;
    const SC_NGROUPS_MAX: c_int = 3;
    const SC_OPEN_MAX: c_int = 4;
    const SC_PAGESIZE: c_int = 30;
    const SC_LINE_MAX: c_int = 43;
    const SC_IOV_MAX: c_int = 60;
    const SC_GETGR_R_SIZE_MAX: c_int = 69;
    const SC_GETPW_R_SIZE_MAX: c_int = 70;
    const SC_LOGIN_NAME_MAX: c_int = 71;
    const SC_TTY_NAME_MAX: c_int = 72;
    const SC_NPROCESSORS_CONF: c_int = 83;
    const SC_NPROCESSORS_ONLN: c_int = 84;
    const SC_PHYS_PAGES: c_int = 85;
    const SC_AVPHYS_PAGES: c_int = 86;
    const SC_MONOTONIC_CLOCK: c_int = 149;
    const SC_SYMLOOP_MAX: c_int = 173;
    const SC_HOST_NAME_MAX: c_int = 180;
    const SC_THREADS: c_int = 67;
    match name {
        SC_ARG_MAX => 131072,
        SC_CHILD_MAX => {
            let mut r = Rlimit {
                rlim_cur: 0,
                rlim_max: 0,
            };
            // SAFETY: valid pointer.
            if unsafe { getrlimit(6, &mut r) } == 0 && r.rlim_cur != u64::MAX {
                r.rlim_cur as c_long
            } else {
                -1
            }
        }
        SC_CLK_TCK => 100,
        SC_NGROUPS_MAX => 32,
        SC_OPEN_MAX => {
            let mut r = Rlimit {
                rlim_cur: 0,
                rlim_max: 0,
            };
            // SAFETY: valid pointer.
            if unsafe { getrlimit(7, &mut r) } == 0 {
                r.rlim_cur.min(c_long::MAX as u64) as c_long
            } else {
                -1
            }
        }
        SC_PAGESIZE => sys::page_size() as c_long,
        SC_LINE_MAX => 4096,
        SC_IOV_MAX => 1024,
        SC_GETGR_R_SIZE_MAX | SC_GETPW_R_SIZE_MAX => 1024,
        SC_LOGIN_NAME_MAX => 256,
        SC_TTY_NAME_MAX => 32,
        SC_NPROCESSORS_CONF | SC_NPROCESSORS_ONLN => cpu_count(),
        SC_PHYS_PAGES | SC_AVPHYS_PAGES => {
            let mut info = SysInfo {
                uptime: 0,
                loads: [0; 3],
                totalram: 0,
                freeram: 0,
                rest: [0; 64],
            };
            // SAFETY: the struct is at least as large as the kernel's.
            if unsafe { sysinfo(&mut info as *mut SysInfo as *mut c_void) } < 0 {
                return -1;
            }
            let bytes = if name == SC_PHYS_PAGES {
                info.totalram
            } else {
                info.freeram
            };
            (bytes / sys::page_size() as u64) as c_long
        }
        SC_MONOTONIC_CLOCK => 200809,
        SC_SYMLOOP_MAX => 40,
        SC_HOST_NAME_MAX => 64,
        SC_THREADS => 200809,
        _ => {
            Errno::EINVAL.set();
            -1
        }
    }
}

/// `struct utsname`.
#[allow(missing_docs)]
#[repr(C)]
pub struct Utsname {
    /// Fields of 65 bytes each: sysname, nodename, release, version,
    /// machine, domainname.
    pub fields: [[u8; 65]; 6],
}

/// `gethostname(2)`.
///
/// # Safety
/// `name` must be valid for `len` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn gethostname(name: *mut c_char, len: usize) -> c_int {
    let mut u = Utsname {
        fields: [[0; 65]; 6],
    };
    // SAFETY: valid pointer.
    if unsafe { uname(&mut u as *mut Utsname as *mut c_void) } < 0 {
        return -1;
    }
    let node = &u.fields[1];
    let n = node.iter().position(|&b| b == 0).unwrap_or(65);
    if n >= len {
        Errno::ENAMETOOLONG.set();
        return -1;
    }
    // SAFETY: caller contract; `n < len`.
    unsafe {
        ptr::copy_nonoverlapping(node.as_ptr(), name as *mut u8, n);
        *name.add(n) = 0;
    }
    0
}

/// `ttyname_r(3)`.
///
/// # Safety
/// `buf` must be valid for `len` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn ttyname_r(fd: c_int, buf: *mut c_char, len: usize) -> c_int {
    if crate::unistd::isatty(fd) == 0 {
        return Errno::ENOTTY.0;
    }
    let mut path = [0u8; 32];
    let mut w = crate::fmt::SliceWriter::new(&mut path);
    let _ = core::fmt::write(&mut w, format_args!("/proc/self/fd/{fd}"));
    // SAFETY: the path is NUL-terminated (the writer keeps one byte spare).
    let n = unsafe { readlink(path.as_ptr() as *const c_char, buf, len) };
    if n < 0 {
        return Errno::get().0;
    }
    if n as usize >= len {
        return Errno::ERANGE.0;
    }
    // SAFETY: `n < len`.
    unsafe { *buf.add(n as usize) = 0 };
    0
}

/// `ttyname(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn ttyname(fd: c_int) -> *mut c_char {
    // SAFETY: the TCB is valid for the life of the thread.
    let buf = unsafe { &mut (*crate::thread::current()).path_buf };
    // SAFETY: the buffer is valid.
    let r = unsafe { ttyname_r(fd, buf.as_mut_ptr() as *mut c_char, buf.len()) };
    if r != 0 {
        Errno(r).set();
        return ptr::null_mut();
    }
    buf.as_mut_ptr() as *mut c_char
}

/// `realpath(3)`: resolves through `/proc/self/fd`, which gives the
/// canonical path for anything that can be opened with `O_PATH`.
///
/// # Safety
/// `path` must be NUL-terminated; `resolved` null or `PATH_MAX` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn realpath(path: *const c_char, resolved: *mut c_char) -> *mut c_char {
    // SAFETY: forwarded.
    let fd = unsafe { openat(AT_FDCWD, path, sys::O_PATH | sys::O_CLOEXEC, 0) };
    if fd < 0 {
        return ptr::null_mut();
    }
    let mut link = [0u8; 32];
    let mut w = crate::fmt::SliceWriter::new(&mut link);
    let _ = core::fmt::write(&mut w, format_args!("/proc/self/fd/{fd}"));
    let mut tmp = [0u8; 4096];
    // SAFETY: NUL-terminated path and a valid buffer.
    let n = unsafe {
        readlink(
            link.as_ptr() as *const c_char,
            tmp.as_mut_ptr() as *mut c_char,
            tmp.len(),
        )
    };
    let _ = sys::close(fd);
    if n < 0 {
        return ptr::null_mut();
    }
    let n = n as usize;
    if n >= tmp.len() || tmp[0] != b'/' {
        Errno::ENAMETOOLONG.set();
        return ptr::null_mut();
    }
    // The link target may report a deleted file; check it still exists.
    tmp[n] = 0;
    let mut st = Stat::default();
    // SAFETY: valid pointers.
    if unsafe { fstatat(AT_FDCWD, tmp.as_ptr() as *const c_char, &mut st, 0) } < 0 {
        return ptr::null_mut();
    }
    let out = if resolved.is_null() {
        malloc::alloc(n + 1) as *mut c_char
    } else {
        resolved
    };
    if out.is_null() {
        return out;
    }
    // SAFETY: `out` has room for `n + 1` bytes.
    unsafe { ptr::copy_nonoverlapping(tmp.as_ptr(), out as *mut u8, n + 1) };
    out
}

/// Checks a `mkstemp`-style template and returns the index of its
/// `XXXXXX` suffix.
///
/// # Safety
/// `template` must be NUL-terminated.
unsafe fn template_suffix(template: *mut c_char) -> Option<usize> {
    // SAFETY: caller contract.
    let len = unsafe { crate::string::search::strlen(template as *const u8) };
    if len < 6 {
        return None;
    }
    // SAFETY: as above.
    let s = unsafe { core::slice::from_raw_parts(template as *const u8, len) };
    if &s[len - 6..] != b"XXXXXX" {
        return None;
    }
    Some(len - 6)
}

/// `mkostemp(3)`.
///
/// # Safety
/// `template` must be a writable NUL-terminated string.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mkostemp(template: *mut c_char, flags: c_int) -> c_int {
    // SAFETY: forwarded.
    let Some(pos) = (unsafe { template_suffix(template) }) else {
        Errno::EINVAL.set();
        return -1;
    };
    for _ in 0..100 {
        // SAFETY: the suffix is inside the string.
        let suffix = unsafe { core::slice::from_raw_parts_mut((template as *mut u8).add(pos), 6) };
        if let Err(e) = crate::stdio::randomize(suffix) {
            e.set();
            return -1;
        }
        // SAFETY: forwarded.
        let fd = unsafe {
            openat(
                AT_FDCWD,
                template,
                (flags & (sys::O_APPEND | sys::O_CLOEXEC | sys::O_SYNC))
                    | sys::O_RDWR
                    | sys::O_CREAT
                    | sys::O_EXCL,
                0o600,
            )
        };
        if fd >= 0 || Errno::get() != Errno::EEXIST {
            return fd;
        }
    }
    Errno::EEXIST.set();
    -1
}

/// `mkstemp(3)`.
///
/// # Safety
/// As for [`mkostemp`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mkstemp(template: *mut c_char) -> c_int {
    // SAFETY: forwarded.
    unsafe { mkostemp(template, 0) }
}

/// `mkdtemp(3)`.
///
/// # Safety
/// As for [`mkostemp`].
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn mkdtemp(template: *mut c_char) -> *mut c_char {
    // SAFETY: forwarded.
    let Some(pos) = (unsafe { template_suffix(template) }) else {
        Errno::EINVAL.set();
        return ptr::null_mut();
    };
    for _ in 0..100 {
        // SAFETY: the suffix is inside the string.
        let suffix = unsafe { core::slice::from_raw_parts_mut((template as *mut u8).add(pos), 6) };
        if let Err(e) = crate::stdio::randomize(suffix) {
            e.set();
            return ptr::null_mut();
        }
        // SAFETY: forwarded.
        if unsafe { mkdirat(AT_FDCWD, template, 0o700) } == 0 {
            return template;
        }
        if Errno::get() != Errno::EEXIST {
            return ptr::null_mut();
        }
    }
    Errno::EEXIST.set();
    ptr::null_mut()
}

/// `getrandom(2)`.
///
/// # Safety
/// `buf` must be valid for `len` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getrandom(buf: *mut c_void, len: usize, flags: c_uint) -> isize {
    // SAFETY: caller contract.
    let r = unsafe { crate::arch::syscall3(nr::GETRANDOM, buf as usize, len, flags as usize) };
    sys::check(r).c_ret()
}

/// `getentropy(3)`.
///
/// # Safety
/// `buf` must be valid for `len` bytes.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn getentropy(buf: *mut c_void, len: usize) -> c_int {
    if len > 256 {
        Errno::EIO.set();
        return -1;
    }
    // SAFETY: caller contract.
    let slice = unsafe { core::slice::from_raw_parts_mut(buf as *mut u8, len) };
    sys::getrandom_exact(slice).c_ret()
}

/// `syscall(2)`: the six possible arguments are read from the registers
/// variadic arguments are passed in.
///
/// # Safety
/// As for the system call being made.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn syscall(
    num: c_long,
    a1: usize,
    a2: usize,
    a3: usize,
    a4: usize,
    a5: usize,
    a6: usize,
) -> c_long {
    // SAFETY: caller contract.
    let r = unsafe { crate::arch::syscall6(num as usize, a1, a2, a3, a4, a5, a6) };
    sys::check(r).map(|v| v as c_long).c_ret_or(-1)
}

/// `daemon(3)`.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub extern "C" fn daemon(nochdir: c_int, noclose: c_int) -> c_int {
    match crate::process::fork() {
        -1 => return -1,
        0 => {}
        _ => crate::exit::_exit(0),
    }
    if crate::unistd::setsid() < 0 {
        return -1;
    }
    // SAFETY: literal path.
    if nochdir == 0 && unsafe { chdir(c"/".as_ptr()) } < 0 {
        return -1;
    }
    if noclose == 0 {
        // SAFETY: literal path.
        let fd = unsafe { openat(AT_FDCWD, c"/dev/null".as_ptr(), sys::O_RDWR, 0) };
        if fd < 0 {
            return -1;
        }
        for target in 0..3 {
            if crate::unistd::dup2(fd, target) < 0 {
                return -1;
            }
        }
        if fd > 2 {
            let _ = sys::close(fd);
        }
    }
    0
}

/// `basename(3)` (the POSIX variant that may modify its argument).
///
/// # Safety
/// `path` must be null or a writable NUL-terminated string.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn basename(path: *mut c_char) -> *mut c_char {
    if path.is_null() {
        return c".".as_ptr() as *mut c_char;
    }
    // SAFETY: caller contract.
    unsafe {
        let mut len = crate::string::search::strlen(path as *const u8);
        if len == 0 {
            return c".".as_ptr() as *mut c_char;
        }
        // Strip trailing slashes.
        while len > 1 && *path.add(len - 1) == b'/' as c_char {
            len -= 1;
            *path.add(len) = 0;
        }
        if len == 1 && *path == b'/' as c_char {
            return path;
        }
        let bytes = core::slice::from_raw_parts(path as *const u8, len);
        match crate::string::search::memrchr(bytes, b'/') {
            Some(i) => path.add(i + 1),
            None => path,
        }
    }
}

/// `dirname(3)`.
///
/// # Safety
/// `path` must be null or a writable NUL-terminated string.
#[cfg_attr(not(test), unsafe(no_mangle))]
pub unsafe extern "C" fn dirname(path: *mut c_char) -> *mut c_char {
    if path.is_null() {
        return c".".as_ptr() as *mut c_char;
    }
    // SAFETY: caller contract.
    unsafe {
        let mut len = crate::string::search::strlen(path as *const u8);
        if len == 0 {
            return c".".as_ptr() as *mut c_char;
        }
        while len > 1 && *path.add(len - 1) == b'/' as c_char {
            len -= 1;
        }
        let bytes = core::slice::from_raw_parts(path as *const u8, len);
        let Some(mut i) = crate::string::search::memrchr(bytes, b'/') else {
            return c".".as_ptr() as *mut c_char;
        };
        while i > 0 && *path.add(i - 1) == b'/' as c_char {
            i -= 1;
        }
        if i == 0 {
            *path.add(1) = 0;
            return path;
        }
        *path.add(i) = 0;
        path
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::{CStr, CString};

    fn bn(s: &str) -> String {
        let mut c = CString::new(s).unwrap().into_bytes_with_nul();
        // SAFETY: NUL-terminated, writable.
        unsafe {
            CStr::from_ptr(basename(c.as_mut_ptr() as *mut c_char))
                .to_str()
                .unwrap()
                .to_string()
        }
    }
    fn dn(s: &str) -> String {
        let mut c = CString::new(s).unwrap().into_bytes_with_nul();
        // SAFETY: NUL-terminated, writable.
        unsafe {
            CStr::from_ptr(dirname(c.as_mut_ptr() as *mut c_char))
                .to_str()
                .unwrap()
                .to_string()
        }
    }

    #[test]
    fn base_and_dir_names() {
        for (path, base, dir) in [
            ("/usr/lib", "lib", "/usr"),
            ("/usr/", "usr", "/"),
            ("usr", "usr", "."),
            ("/", "/", "/"),
            (".", ".", "."),
            ("..", "..", "."),
            ("", ".", "."),
            ("//", "/", "/"),
            ("a/b//", "b", "a"),
            ("/a", "a", "/"),
            ("a//b", "b", "a"),
        ] {
            assert_eq!(bn(path), base, "basename({path:?})");
            assert_eq!(dn(path), dir, "dirname({path:?})");
        }
    }

    #[test]
    fn stat_and_realpath() {
        let mut st = Stat::default();
        // SAFETY: valid pointers.
        unsafe {
            assert_eq!(stat(c"/".as_ptr(), &mut st), 0);
            assert_eq!(st.st_mode & 0o170000, 0o040000);
            assert_eq!(stat(c"/nonexistent-xyz".as_ptr(), &mut st), -1);
            assert_eq!(Errno::get(), Errno::ENOENT);
            let p = realpath(c"/usr/../usr/./bin/.".as_ptr(), ptr::null_mut());
            assert!(!p.is_null());
            assert_eq!(CStr::from_ptr(p).to_str().unwrap(), "/usr/bin");
            malloc::dealloc(p as *mut u8);
        }
        assert!(sysconf(30) == 4096);
        assert!(sysconf(84) >= 1);
        assert!(sysconf(85) > 0);
        assert_eq!(sysconf(9999), -1);
    }

    #[test]
    fn temp_files() {
        let mut t = *b"/tmp/rustlibc-test-XXXXXX\0";
        // SAFETY: writable NUL-terminated template.
        unsafe {
            let fd = mkstemp(t.as_mut_ptr() as *mut c_char);
            assert!(fd >= 0);
            assert_ne!(&t[19..25], b"XXXXXX");
            let _ = sys::close(fd);
            assert_eq!(unlink(t.as_ptr() as *const c_char), 0);
            let mut bad = *b"nope\0";
            assert_eq!(mkstemp(bad.as_mut_ptr() as *mut c_char), -1);
            let mut d = *b"/tmp/rustlibc-dir-XXXXXX\0";
            assert!(!mkdtemp(d.as_mut_ptr() as *mut c_char).is_null());
            assert_eq!(rmdir(d.as_ptr() as *const c_char), 0);
        }
    }
}
