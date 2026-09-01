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

ssize_t read(int, void *, size_t);
ssize_t write(int, const void *, size_t);
int close(int);
pid_t getpid(void);
pid_t gettid(void);
__NORETURN void _exit(int);

extern char **environ;

__END_DECLS

#endif
