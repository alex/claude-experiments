#ifndef _FCNTL_H
#define _FCNTL_H
#include <bits/features.h>

#define __NEED_off_t
#define __NEED_pid_t
#define __NEED_mode_t
#include <bits/alltypes.h>

#define O_RDONLY 00
#define O_WRONLY 01
#define O_RDWR 02
#define O_ACCMODE 03
#define O_CREAT 0100
#define O_EXCL 0200
#define O_NOCTTY 0400
#define O_TRUNC 01000
#define O_APPEND 02000
#define O_NONBLOCK 04000
#define O_NDELAY O_NONBLOCK
#define O_DSYNC 010000
#define O_ASYNC 020000
#if defined(__x86_64__)
#define O_DIRECT 040000
#define O_LARGEFILE 0100000
#define O_DIRECTORY 0200000
#define O_NOFOLLOW 0400000
#else
#define O_DIRECTORY 040000
#define O_NOFOLLOW 0100000
#define O_DIRECT 0200000
#define O_LARGEFILE 0400000
#endif
#define O_NOATIME 01000000
#define O_CLOEXEC 02000000
#define O_SYNC 04010000
#define O_RSYNC O_SYNC
#define O_PATH 010000000
#define O_TMPFILE 020200000

#define F_DUPFD 0
#define F_GETFD 1
#define F_SETFD 2
#define F_GETFL 3
#define F_SETFL 4
#define F_GETLK 5
#define F_SETLK 6
#define F_SETLKW 7
#define F_SETOWN 8
#define F_GETOWN 9
#define F_DUPFD_CLOEXEC 1030
#define F_GETPIPE_SZ 1032
#define F_SETPIPE_SZ 1031
#define FD_CLOEXEC 1

#define F_RDLCK 0
#define F_WRLCK 1
#define F_UNLCK 2

#define AT_FDCWD (-100)
#define AT_SYMLINK_NOFOLLOW 0x100
#define AT_REMOVEDIR 0x200
#define AT_SYMLINK_FOLLOW 0x400
#define AT_EACCESS 0x200
#define AT_EMPTY_PATH 0x1000

#define FALLOC_FL_KEEP_SIZE 1
#define FALLOC_FL_PUNCH_HOLE 2
#define POSIX_FADV_NORMAL 0
#define POSIX_FADV_RANDOM 1
#define POSIX_FADV_SEQUENTIAL 2
#define POSIX_FADV_WILLNEED 3
#define POSIX_FADV_DONTNEED 4
#define POSIX_FADV_NOREUSE 5

struct flock {
    short l_type;
    short l_whence;
    off_t l_start;
    off_t l_len;
    pid_t l_pid;
};

__BEGIN_DECLS
int open(const char *, int, ...);
int openat(int, const char *, int, ...);
int creat(const char *, mode_t);
int fcntl(int, int, ...);
int posix_fadvise(int, off_t, off_t, int);
int posix_fallocate(int, off_t, off_t);
int fallocate(int, int, off_t, off_t);
__END_DECLS

#endif
