#ifndef _SYS_WAIT_H
#define _SYS_WAIT_H
#include <bits/features.h>

#define __NEED_pid_t
#define __NEED_id_t
#include <bits/alltypes.h>
#include <signal.h>

typedef enum { P_ALL, P_PID, P_PGID, P_PIDFD } idtype_t;
typedef int id_t;

#define WNOHANG 1
#define WUNTRACED 2
#define WSTOPPED 2
#define WEXITED 4
#define WCONTINUED 8
#define WNOWAIT 0x01000000

#define WEXITSTATUS(s) (((s) & 0xff00) >> 8)
#define WTERMSIG(s) ((s) & 0x7f)
#define WSTOPSIG(s) WEXITSTATUS(s)
#define WCOREDUMP(s) ((s) & 0x80)
#define WIFEXITED(s) (!WTERMSIG(s))
#define WIFSTOPPED(s) ((short)((((s) & 0xffff) * 0x10001) >> 8) > 0x7f00)
#define WIFSIGNALED(s) (((s) & 0xffff) - 1U < 0xffu)
#define WIFCONTINUED(s) ((s) == 0xffff)

__BEGIN_DECLS

pid_t wait(int *);
pid_t waitpid(pid_t, int *, int);
int waitid(idtype_t, id_t, siginfo_t *, int);
pid_t wait4(pid_t, int *, int, void *);

__END_DECLS

#endif
