#ifndef _SIGNAL_H
#define _SIGNAL_H
#include <bits/features.h>

#define __NEED_size_t
#define __NEED_pid_t
#define __NEED_uid_t
#define __NEED_time_t
#define __NEED_struct_timespec
#define __NEED_sigset_t
#include <bits/alltypes.h>

typedef int sig_atomic_t;

union sigval { int sival_int; void *sival_ptr; };

typedef struct {
    int si_signo, si_errno, si_code;
    union {
        char __pad[128 - 2 * sizeof(int) - sizeof(long)];
        struct { pid_t si_pid; uid_t si_uid; union sigval si_value; } __kill;
        struct { void *si_timerid; int si_overrun; union sigval si_value; } __timer;
        struct { pid_t si_pid; uid_t si_uid; int si_status; long si_utime, si_stime; } __chld;
        struct { void *si_addr; short si_addr_lsb; } __fault;
        struct { long si_band; int si_fd; } __poll;
        struct { void *si_call_addr; int si_syscall; unsigned si_arch; } __sys;
    } __si_fields;
} siginfo_t;
#define si_pid __si_fields.__kill.si_pid
#define si_uid __si_fields.__kill.si_uid
#define si_value __si_fields.__kill.si_value
#define si_status __si_fields.__chld.si_status
#define si_addr __si_fields.__fault.si_addr
#define si_band __si_fields.__poll.si_band
#define si_fd __si_fields.__poll.si_fd

struct sigaction {
    union {
        void (*sa_handler)(int);
        void (*sa_sigaction)(int, siginfo_t *, void *);
    } __sa_handler;
    sigset_t sa_mask;
    int sa_flags;
    void (*sa_restorer)(void);
};
#define sa_handler __sa_handler.sa_handler
#define sa_sigaction __sa_handler.sa_sigaction

typedef struct {
    void *ss_sp;
    int ss_flags;
    size_t ss_size;
} stack_t;

typedef void (*sighandler_t)(int);
#define SIG_DFL ((void (*)(int))0)
#define SIG_IGN ((void (*)(int))1)
#define SIG_ERR ((void (*)(int))-1)

#define SIGHUP 1
#define SIGINT 2
#define SIGQUIT 3
#define SIGILL 4
#define SIGTRAP 5
#define SIGABRT 6
#define SIGIOT 6
#define SIGBUS 7
#define SIGFPE 8
#define SIGKILL 9
#define SIGUSR1 10
#define SIGSEGV 11
#define SIGUSR2 12
#define SIGPIPE 13
#define SIGALRM 14
#define SIGTERM 15
#define SIGSTKFLT 16
#define SIGCHLD 17
#define SIGCONT 18
#define SIGSTOP 19
#define SIGTSTP 20
#define SIGTTIN 21
#define SIGTTOU 22
#define SIGURG 23
#define SIGXCPU 24
#define SIGXFSZ 25
#define SIGVTALRM 26
#define SIGPROF 27
#define SIGWINCH 28
#define SIGIO 29
#define SIGPOLL 29
#define SIGPWR 30
#define SIGSYS 31
#define SIGRTMIN 32
#define SIGRTMAX 64
#define NSIG 65
#define _NSIG 65

#define SA_NOCLDSTOP 1
#define SA_NOCLDWAIT 2
#define SA_SIGINFO 4
#define SA_ONSTACK 0x08000000
#define SA_RESTART 0x10000000
#define SA_NODEFER 0x40000000
#define SA_RESETHAND 0x80000000
#define SA_NOMASK SA_NODEFER
#define SA_ONESHOT SA_RESETHAND

#define SIG_BLOCK 0
#define SIG_UNBLOCK 1
#define SIG_SETMASK 2

#define SS_ONSTACK 1
#define SS_DISABLE 2
#define MINSIGSTKSZ 2048
#define SIGSTKSZ 8192

#define SI_USER 0
#define SI_KERNEL 128
#define SI_QUEUE (-1)
#define SI_TIMER (-2)
#define SI_TKILL (-6)
#define CLD_EXITED 1
#define CLD_KILLED 2
#define CLD_DUMPED 3
#define CLD_STOPPED 5
#define CLD_CONTINUED 6
#define SEGV_MAPERR 1
#define SEGV_ACCERR 2

__BEGIN_DECLS

int sigemptyset(sigset_t *);
int sigfillset(sigset_t *);
int sigaddset(sigset_t *, int);
int sigdelset(sigset_t *, int);
int sigismember(const sigset_t *, int);
int sigisemptyset(const sigset_t *);
int sigaction(int, const struct sigaction *__RESTRICT, struct sigaction *__RESTRICT);
void (*signal(int, void (*)(int)))(int);
int sigprocmask(int, const sigset_t *__RESTRICT, sigset_t *__RESTRICT);
int pthread_sigmask(int, const sigset_t *__RESTRICT, sigset_t *__RESTRICT);
int kill(pid_t, int);
int killpg(pid_t, int);
int raise(int);
int sigsuspend(const sigset_t *);
int sigpending(sigset_t *);
int sigwait(const sigset_t *__RESTRICT, int *__RESTRICT);
int sigwaitinfo(const sigset_t *__RESTRICT, siginfo_t *__RESTRICT);
int sigtimedwait(const sigset_t *__RESTRICT, siginfo_t *__RESTRICT, const struct timespec *__RESTRICT);
int sigaltstack(const stack_t *__RESTRICT, stack_t *__RESTRICT);
int siginterrupt(int, int);
char *strsignal(int);
void psignal(int, const char *);

__END_DECLS

#endif
