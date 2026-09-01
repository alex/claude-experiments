#ifndef _UNISTD_H
#define _UNISTD_H
#include <bits/features.h>

#define __NEED_size_t
#define __NEED_ssize_t
#define __NEED_off_t
#define __NEED_pid_t
#define __NEED_uid_t
#define __NEED_gid_t
#include <bits/alltypes.h>

#ifdef __cplusplus
#define NULL 0L
#else
#define NULL ((void *)0)
#endif

#define STDIN_FILENO 0
#define STDOUT_FILENO 1
#define STDERR_FILENO 2

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

__END_DECLS

#endif
