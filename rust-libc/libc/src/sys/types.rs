//! Kernel ABI data structures shared by several modules.
//!
//! Layouts follow the x86_64 Linux UAPI headers. The C headers under
//! `include/` mirror these definitions; `tests/c/abi_layout.c` checks that
//! the two agree.
#![allow(missing_docs)]

use core::ffi::{c_int, c_long};

/// `struct timespec`.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Timespec {
    pub tv_sec: i64,
    pub tv_nsec: c_long,
}

/// `PROT_*` flags for `mmap` and `mprotect`.
pub const PROT_NONE: c_int = 0;
pub const PROT_READ: c_int = 1;
pub const PROT_WRITE: c_int = 2;
pub const PROT_EXEC: c_int = 4;

/// `MAP_*` flags for `mmap`.
pub const MAP_SHARED: c_int = 0x01;
pub const MAP_PRIVATE: c_int = 0x02;
pub const MAP_FIXED: c_int = 0x10;
pub const MAP_ANONYMOUS: c_int = 0x20;
pub const MAP_GROWSDOWN: c_int = 0x100;
pub const MAP_NORESERVE: c_int = 0x4000;
pub const MAP_POPULATE: c_int = 0x8000;
pub const MAP_STACK: c_int = 0x20000;

/// The page size on x86_64. Linux on x86_64 only supports 4 KiB pages.
pub const PAGE_SIZE: usize = 4096;

/// Signal numbers.
pub const SIGHUP: c_int = 1;
pub const SIGINT: c_int = 2;
pub const SIGQUIT: c_int = 3;
pub const SIGILL: c_int = 4;
pub const SIGTRAP: c_int = 5;
pub const SIGABRT: c_int = 6;
pub const SIGBUS: c_int = 7;
pub const SIGFPE: c_int = 8;
pub const SIGKILL: c_int = 9;
pub const SIGUSR1: c_int = 10;
pub const SIGSEGV: c_int = 11;
pub const SIGUSR2: c_int = 12;
pub const SIGPIPE: c_int = 13;
pub const SIGALRM: c_int = 14;
pub const SIGTERM: c_int = 15;
pub const SIGSTKFLT: c_int = 16;
pub const SIGCHLD: c_int = 17;
pub const SIGCONT: c_int = 18;
pub const SIGSTOP: c_int = 19;
pub const SIGTSTP: c_int = 20;
pub const SIGTTIN: c_int = 21;
pub const SIGTTOU: c_int = 22;
pub const SIGURG: c_int = 23;
pub const SIGXCPU: c_int = 24;
pub const SIGXFSZ: c_int = 25;
pub const SIGVTALRM: c_int = 26;
pub const SIGPROF: c_int = 27;
pub const SIGWINCH: c_int = 28;
pub const SIGIO: c_int = 29;
pub const SIGPWR: c_int = 30;
pub const SIGSYS: c_int = 31;

/// `how` arguments for `rt_sigprocmask`.
pub const SIG_BLOCK: c_int = 0;
pub const SIG_UNBLOCK: c_int = 1;
pub const SIG_SETMASK: c_int = 2;

/// `open(2)` flags (x86_64 values).
pub const O_RDONLY: c_int = 0;
pub const O_WRONLY: c_int = 1;
pub const O_RDWR: c_int = 2;
pub const O_ACCMODE: c_int = 3;
pub const O_CREAT: c_int = 0o100;
pub const O_EXCL: c_int = 0o200;
pub const O_NOCTTY: c_int = 0o400;
pub const O_TRUNC: c_int = 0o1000;
pub const O_APPEND: c_int = 0o2000;
pub const O_NONBLOCK: c_int = 0o4000;
pub const O_DSYNC: c_int = 0o10000;
pub const O_ASYNC: c_int = 0o20000;
#[cfg(target_arch = "x86_64")]
pub const O_DIRECT: c_int = 0o40000;
#[cfg(target_arch = "x86_64")]
pub const O_LARGEFILE: c_int = 0o100000;
#[cfg(target_arch = "x86_64")]
pub const O_DIRECTORY: c_int = 0o200000;
#[cfg(target_arch = "x86_64")]
pub const O_NOFOLLOW: c_int = 0o400000;
// The asm-generic values (aarch64).
#[cfg(not(target_arch = "x86_64"))]
pub const O_DIRECTORY: c_int = 0o40000;
#[cfg(not(target_arch = "x86_64"))]
pub const O_NOFOLLOW: c_int = 0o100000;
#[cfg(not(target_arch = "x86_64"))]
pub const O_DIRECT: c_int = 0o200000;
#[cfg(not(target_arch = "x86_64"))]
pub const O_LARGEFILE: c_int = 0o400000;
pub const O_NOATIME: c_int = 0o1000000;
pub const O_CLOEXEC: c_int = 0o2000000;
pub const O_SYNC: c_int = 0o4010000;
pub const O_PATH: c_int = 0o10000000;
pub const O_TMPFILE: c_int = 0o20200000;

/// Special `dirfd` meaning the current working directory.
pub const AT_FDCWD: c_int = -100;
pub const AT_REMOVEDIR: c_int = 0x200;

/// `lseek(2)` whence values.
pub const SEEK_SET: c_int = 0;
pub const SEEK_CUR: c_int = 1;
pub const SEEK_END: c_int = 2;

/// `ioctl` request to read terminal attributes; used by `isatty`.
pub const TCGETS: usize = 0x5401;

/// `fcntl` commands.
pub const F_DUPFD: c_int = 0;
pub const F_GETFD: c_int = 1;
pub const F_SETFD: c_int = 2;
pub const F_GETFL: c_int = 3;
pub const F_SETFL: c_int = 4;
pub const FD_CLOEXEC: c_int = 1;

/// Clock ids.
pub const CLOCK_REALTIME: c_int = 0;
pub const CLOCK_MONOTONIC: c_int = 1;
pub const CLOCK_PROCESS_CPUTIME_ID: c_int = 2;
pub const CLOCK_THREAD_CPUTIME_ID: c_int = 3;
pub const CLOCK_MONOTONIC_RAW: c_int = 4;
pub const CLOCK_REALTIME_COARSE: c_int = 5;
pub const CLOCK_MONOTONIC_COARSE: c_int = 6;
pub const CLOCK_BOOTTIME: c_int = 7;

/// `clone(2)` flags.
pub const CLONE_VM: usize = 0x100;
pub const CLONE_FS: usize = 0x200;
pub const CLONE_FILES: usize = 0x400;
pub const CLONE_SIGHAND: usize = 0x800;
pub const CLONE_THREAD: usize = 0x10000;
pub const CLONE_SYSVSEM: usize = 0x40000;
pub const CLONE_SETTLS: usize = 0x80000;
pub const CLONE_PARENT_SETTID: usize = 0x100000;
pub const CLONE_CHILD_CLEARTID: usize = 0x200000;
pub const CLONE_CHILD_SETTID: usize = 0x1000000;

/// The kernel's `struct sigaction` (x86_64).
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct KernelSigaction {
    pub handler: usize,
    pub flags: u64,
    pub restorer: usize,
    pub mask: u64,
}

/// `sigaction` flags.
pub const SA_NOCLDSTOP: u64 = 1;
pub const SA_NOCLDWAIT: u64 = 2;
pub const SA_SIGINFO: u64 = 4;
pub const SA_ONSTACK: u64 = 0x0800_0000;
pub const SA_RESTART: u64 = 0x1000_0000;
pub const SA_NODEFER: u64 = 0x4000_0000;
pub const SA_RESETHAND: u64 = 0x8000_0000;
pub const SA_RESTORER: u64 = 0x0400_0000;

/// Number of signals (the highest is `NSIG - 1`).
pub const NSIG: c_int = 65;

/// `wait` options.
pub const WNOHANG: c_int = 1;
pub const WUNTRACED: c_int = 2;
