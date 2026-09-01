#ifndef _UNISTD_H
#define _UNISTD_H
#include <bits/features.h>

#define __NEED_size_t
#define __NEED_ssize_t
#define __NEED_off_t
#define __NEED_pid_t
#define __NEED_uid_t
#define __NEED_gid_t
#define __NEED_intptr_t
#include <bits/alltypes.h>

#ifdef __cplusplus
#define NULL 0L
#else
#define NULL ((void *)0)
#endif

#define STDIN_FILENO 0
#define STDOUT_FILENO 1
#define STDERR_FILENO 2

#define F_ULOCK 0
#define F_LOCK 1
#define F_TLOCK 2
#define F_TEST 3

#define _PC_LINK_MAX 0
#define _PC_MAX_CANON 1
#define _PC_MAX_INPUT 2
#define _PC_NAME_MAX 3
#define _PC_PATH_MAX 4
#define _PC_PIPE_BUF 5
#define _PC_CHOWN_RESTRICTED 6
#define _PC_NO_TRUNC 7
#define _PC_VDISABLE 8
#define _PC_REC_XFER_ALIGN 20

#define _CS_PATH 0

__BEGIN_DECLS

unsigned sleep(unsigned);
int usleep(unsigned);
ssize_t read(int, void *, size_t);
ssize_t write(int, const void *, size_t);
ssize_t pread(int, void *, size_t, off_t);
ssize_t pwrite(int, const void *, size_t, off_t);
int close(int);
off_t lseek(int, off_t, int);
int pipe(int[2]);
int pipe2(int[2], int);
int dup(int);
int dup2(int, int);
int dup3(int, int, int);
int isatty(int);
pid_t getppid(void);
uid_t getuid(void);
uid_t geteuid(void);
gid_t getgid(void);
gid_t getegid(void);
int setuid(uid_t);
int setgid(gid_t);
int seteuid(uid_t);
int setegid(gid_t);
pid_t getpgid(pid_t);
int setpgid(pid_t, pid_t);
pid_t getpgrp(void);
pid_t setsid(void);
pid_t getsid(pid_t);
#define SEEK_SET 0
#define SEEK_CUR 1
#define SEEK_END 2
#define F_OK 0
#define X_OK 1
#define W_OK 2
#define R_OK 4

int access(const char *, int);
int faccessat(int, const char *, int, int);
int chdir(const char *);
int fchdir(int);
char *getcwd(char *, size_t);
int rmdir(const char *);
int unlink(const char *);
int unlinkat(int, const char *, int);
int link(const char *, const char *);
int linkat(int, const char *, int, const char *, int);
int symlink(const char *, const char *);
int symlinkat(const char *, int, const char *);
ssize_t readlink(const char *__RESTRICT, char *__RESTRICT, size_t);
ssize_t readlinkat(int, const char *__RESTRICT, char *__RESTRICT, size_t);
int chown(const char *, uid_t, gid_t);
int fchown(int, uid_t, gid_t);
int lchown(const char *, uid_t, gid_t);
int fchownat(int, const char *, uid_t, gid_t, int);
int truncate(const char *, off_t);
int ftruncate(int, off_t);
int fsync(int);
int fdatasync(int);
void sync(void);
int chroot(const char *);
int gethostname(char *, size_t);
char *ttyname(int);
int ttyname_r(int, char *, size_t);
long sysconf(int);
int getpagesize(void);
int nice(int);
int daemon(int, int);
long syscall(long, ...);
int getentropy(void *, size_t);
char *getlogin(void);

extern char *optarg;
extern int optind, opterr, optopt, optreset;
int getopt(int, char *const[], const char *);

#define _SC_ARG_MAX 0
#define _SC_CHILD_MAX 1
#define _SC_CLK_TCK 2
#define _SC_NGROUPS_MAX 3
#define _SC_OPEN_MAX 4
#define _SC_PAGESIZE 30
#define _SC_PAGE_SIZE 30
#define _SC_LINE_MAX 43
#define _SC_IOV_MAX 60
#define _SC_THREADS 67
#define _SC_GETGR_R_SIZE_MAX 69
#define _SC_GETPW_R_SIZE_MAX 70
#define _SC_LOGIN_NAME_MAX 71
#define _SC_TTY_NAME_MAX 72
#define _SC_NPROCESSORS_CONF 83
#define _SC_NPROCESSORS_ONLN 84
#define _SC_PHYS_PAGES 85
#define _SC_AVPHYS_PAGES 86
#define _SC_MONOTONIC_CLOCK 149
#define _SC_SYMLOOP_MAX 173
#define _SC_HOST_NAME_MAX 180

#define _POSIX_VERSION 200809L
#define _XOPEN_VERSION 700
pid_t getpid(void);
pid_t gettid(void);
__NORETURN void _exit(int);
pid_t fork(void);
pid_t vfork(void);
pid_t _Fork(void);
int execve(const char *, char *const[], char *const[]);
int execv(const char *, char *const[]);
int execvp(const char *, char *const[]);
int execvpe(const char *, char *const[], char *const[]);
int execl(const char *, const char *, ...);
int execlp(const char *, const char *, ...);
int execle(const char *, const char *, ...);
int fexecve(int, char *const[], char *const[]);
unsigned alarm(unsigned);
int pause(void);

extern char **environ;

int getgroups(int, gid_t[]);
int setgroups(size_t, const gid_t *);
int getresuid(uid_t *, uid_t *, uid_t *);
int getresgid(gid_t *, gid_t *, gid_t *);
int setresuid(uid_t, uid_t, uid_t);
int setresgid(gid_t, gid_t, gid_t);
int setpgrp(void);
int lockf(int, int, off_t);
long pathconf(const char *, int);
long fpathconf(int, int);
size_t confstr(int, char *, size_t);
int brk(void *);
void *sbrk(intptr_t);
void swab(const void *__RESTRICT, void *__RESTRICT, ssize_t);
int getdtablesize(void);
ssize_t copy_file_range(int, off_t *, int, off_t *, size_t, unsigned);
int sethostname(const char *, size_t);
int getdomainname(char *, size_t);
unsigned ualarm(unsigned, unsigned);
int syncfs(int);
__END_DECLS

#endif
