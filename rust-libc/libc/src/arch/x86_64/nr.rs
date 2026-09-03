//! x86_64 system call numbers (from `arch/x86/entry/syscalls/syscall_64.tbl`).
#![allow(missing_docs)]

pub const READ: usize = 0;
pub const WRITE: usize = 1;
pub const OPEN: usize = 2;
pub const CLOSE: usize = 3;
pub const STAT: usize = 4;
pub const FSTAT: usize = 5;
pub const LSTAT: usize = 6;
pub const POLL: usize = 7;
pub const LSEEK: usize = 8;
pub const MMAP: usize = 9;
pub const MPROTECT: usize = 10;
pub const MUNMAP: usize = 11;
pub const BRK: usize = 12;
pub const RT_SIGACTION: usize = 13;
pub const RT_SIGPROCMASK: usize = 14;
pub const RT_SIGRETURN: usize = 15;
pub const IOCTL: usize = 16;
pub const PREAD64: usize = 17;
pub const PWRITE64: usize = 18;
pub const READV: usize = 19;
pub const WRITEV: usize = 20;
pub const ACCESS: usize = 21;
pub const PIPE: usize = 22;
pub const SELECT: usize = 23;
pub const SCHED_YIELD: usize = 24;
pub const MREMAP: usize = 25;
pub const MSYNC: usize = 26;
pub const MADVISE: usize = 28;
pub const DUP: usize = 32;
pub const DUP2: usize = 33;
pub const PAUSE: usize = 34;
pub const NANOSLEEP: usize = 35;
pub const GETITIMER: usize = 36;
pub const ALARM: usize = 37;
pub const SETITIMER: usize = 38;
pub const GETPID: usize = 39;
pub const SENDFILE: usize = 40;
pub const SOCKET: usize = 41;
pub const CONNECT: usize = 42;
pub const ACCEPT: usize = 43;
pub const SENDTO: usize = 44;
pub const RECVFROM: usize = 45;
pub const SENDMSG: usize = 46;
pub const RECVMSG: usize = 47;
pub const SHUTDOWN: usize = 48;
pub const BIND: usize = 49;
pub const LISTEN: usize = 50;
pub const GETSOCKNAME: usize = 51;
pub const GETPEERNAME: usize = 52;
pub const SOCKETPAIR: usize = 53;
pub const SETSOCKOPT: usize = 54;
pub const GETSOCKOPT: usize = 55;
pub const CLONE: usize = 56;
pub const FORK: usize = 57;
pub const VFORK: usize = 58;
pub const EXECVE: usize = 59;
pub const EXIT: usize = 60;
pub const WAIT4: usize = 61;
pub const KILL: usize = 62;
pub const UNAME: usize = 63;
pub const FCNTL: usize = 72;
pub const FLOCK: usize = 73;
pub const FSYNC: usize = 74;
pub const FDATASYNC: usize = 75;
pub const TRUNCATE: usize = 76;
pub const FTRUNCATE: usize = 77;
pub const GETDENTS: usize = 78;
pub const GETCWD: usize = 79;
pub const CHDIR: usize = 80;
pub const FCHDIR: usize = 81;
pub const RENAME: usize = 82;
pub const MKDIR: usize = 83;
pub const RMDIR: usize = 84;
pub const CREAT: usize = 85;
pub const LINK: usize = 86;
pub const UNLINK: usize = 87;
pub const SYMLINK: usize = 88;
pub const READLINK: usize = 89;
pub const CHMOD: usize = 90;
pub const FCHMOD: usize = 91;
pub const CHOWN: usize = 92;
pub const FCHOWN: usize = 93;
pub const LCHOWN: usize = 94;
pub const UMASK: usize = 95;
pub const GETTIMEOFDAY: usize = 96;
pub const GETRLIMIT: usize = 97;
pub const GETRUSAGE: usize = 98;
pub const SYSINFO: usize = 99;
pub const TIMES: usize = 100;
pub const GETUID: usize = 102;
pub const GETGID: usize = 104;
pub const SETUID: usize = 105;
pub const SETGID: usize = 106;
pub const GETEUID: usize = 107;
pub const GETEGID: usize = 108;
pub const SETPGID: usize = 109;
pub const GETPPID: usize = 110;
pub const GETPGRP: usize = 111;
pub const SETSID: usize = 112;
pub const GETPGID: usize = 121;
pub const GETSID: usize = 124;
pub const RT_SIGPENDING: usize = 127;
pub const RT_SIGTIMEDWAIT: usize = 128;
pub const RT_SIGSUSPEND: usize = 130;
pub const SIGALTSTACK: usize = 131;
pub const UTIME: usize = 132;
pub const MKNOD: usize = 133;
pub const STATFS: usize = 137;
pub const FSTATFS: usize = 138;
pub const PRCTL: usize = 157;
pub const ARCH_PRCTL: usize = 158;
pub const SETRLIMIT: usize = 160;
pub const CHROOT: usize = 161;
pub const SYNC: usize = 162;
pub const GETTID: usize = 186;
pub const TKILL: usize = 200;
pub const TIME: usize = 201;
pub const FUTEX: usize = 202;
pub const SCHED_SETAFFINITY: usize = 203;
pub const SCHED_GETAFFINITY: usize = 204;
pub const GETDENTS64: usize = 217;
pub const SET_TID_ADDRESS: usize = 218;
pub const CLOCK_SETTIME: usize = 227;
pub const CLOCK_GETTIME: usize = 228;
pub const CLOCK_GETRES: usize = 229;
pub const CLOCK_NANOSLEEP: usize = 230;
pub const EXIT_GROUP: usize = 231;
pub const TGKILL: usize = 234;
pub const OPENAT: usize = 257;
pub const MKDIRAT: usize = 258;
pub const FCHOWNAT: usize = 260;
pub const NEWFSTATAT: usize = 262;
pub const UNLINKAT: usize = 263;
pub const RENAMEAT: usize = 264;
pub const LINKAT: usize = 265;
pub const SYMLINKAT: usize = 266;
pub const READLINKAT: usize = 267;
pub const FCHMODAT: usize = 268;
pub const FACCESSAT: usize = 269;
pub const PSELECT6: usize = 270;
pub const PPOLL: usize = 271;
pub const SET_ROBUST_LIST: usize = 273;
pub const UTIMENSAT: usize = 280;
pub const ACCEPT4: usize = 288;
pub const EVENTFD2: usize = 290;
pub const DUP3: usize = 292;
pub const PIPE2: usize = 293;
pub const PREADV: usize = 295;
pub const PWRITEV: usize = 296;
pub const PRLIMIT64: usize = 302;
pub const GETRANDOM: usize = 318;
pub const MEMFD_CREATE: usize = 319;
pub const STATX: usize = 332;
pub const RSEQ: usize = 334;
pub const CLONE3: usize = 435;
pub const FACCESSAT2: usize = 439;
#[allow(missing_docs)]
pub const RENAMEAT2: usize = 316;
#[allow(missing_docs)]
pub const EPOLL_CREATE1: usize = 291;
#[allow(missing_docs)]
pub const EPOLL_CTL: usize = 233;
#[allow(missing_docs)]
pub const GETGROUPS: usize = 115;
#[allow(missing_docs)]
pub const SETGROUPS: usize = 116;
#[allow(missing_docs)]
pub const SETRESUID: usize = 117;
#[allow(missing_docs)]
pub const SETRESGID: usize = 119;
#[allow(missing_docs)]
pub const FALLOCATE: usize = 285;
#[allow(missing_docs)]
pub const SETHOSTNAME: usize = 170;
#[allow(missing_docs)]
pub const SYNCFS: usize = 306;
#[allow(missing_docs)]
pub const EXECVEAT: usize = 322;
#[allow(missing_docs)]
pub const WAITID: usize = 247;
#[allow(missing_docs)]
pub const MLOCK: usize = 149;
#[allow(missing_docs)]
pub const MUNLOCK: usize = 150;
#[allow(missing_docs)]
pub const MKNODAT: usize = 259;
#[allow(missing_docs)]
pub const GETPRIORITY: usize = 140;
#[allow(missing_docs)]
pub const SETPRIORITY: usize = 141;
#[allow(missing_docs)]
pub const TIMERFD_CREATE: usize = 283;
#[allow(missing_docs)]
pub const EPOLL_PWAIT: usize = 281;
#[allow(missing_docs)]
pub const GETCPU: usize = 309;
#[allow(missing_docs)]
pub const SCHED_SETPARAM: usize = 142;
#[allow(missing_docs)]
pub const SCHED_GETPARAM: usize = 143;
#[allow(missing_docs)]
pub const SCHED_SETSCHEDULER: usize = 144;
#[allow(missing_docs)]
pub const SCHED_GETSCHEDULER: usize = 145;
#[allow(missing_docs)]
pub const SCHED_GET_PRIORITY_MAX: usize = 146;
#[allow(missing_docs)]
pub const SCHED_GET_PRIORITY_MIN: usize = 147;
#[allow(missing_docs)]
pub const SCHED_RR_GET_INTERVAL: usize = 148;
#[allow(missing_docs)]
pub const TIMERFD_SETTIME: usize = 286;
#[allow(missing_docs)]
pub const TIMERFD_GETTIME: usize = 287;
#[allow(missing_docs)]
pub const FADVISE64: usize = 221;
#[allow(missing_docs)]
pub const COPY_FILE_RANGE: usize = 326;
#[allow(missing_docs)]
pub const SIGNALFD4: usize = 289;
#[allow(missing_docs)]
pub const INOTIFY_INIT1: usize = 294;
#[allow(missing_docs)]
pub const INOTIFY_ADD_WATCH: usize = 254;
#[allow(missing_docs)]
pub const INOTIFY_RM_WATCH: usize = 255;
#[allow(missing_docs)]
pub const MLOCKALL: usize = 151;
#[allow(missing_docs)]
pub const MUNLOCKALL: usize = 152;
#[allow(missing_docs)]
pub const GETRESUID: usize = 118;
#[allow(missing_docs)]
pub const GETRESGID: usize = 120;
