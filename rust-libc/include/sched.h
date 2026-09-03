#ifndef _SCHED_H
#define _SCHED_H
#include <bits/features.h>

#define __NEED_pid_t
#define __NEED_size_t
#define __NEED_time_t
#define __NEED_struct_timespec
#include <bits/alltypes.h>

struct sched_param { int sched_priority; };

#define SCHED_OTHER 0
#define SCHED_FIFO 1
#define SCHED_RR 2

#define SCHED_BATCH 3
#define SCHED_IDLE 5
#define SCHED_DEADLINE 6
#define SCHED_RESET_ON_FORK 0x40000000

#define CPU_SETSIZE 1024
typedef struct cpu_set_t { unsigned long __bits[CPU_SETSIZE / (8 * sizeof(unsigned long))]; } cpu_set_t;
#define __CPU_op(i, set, op) ((set)->__bits[(i) / (8 * sizeof(unsigned long))] op (1UL << ((i) % (8 * sizeof(unsigned long)))))
#define CPU_SET(i, set) ((void)__CPU_op(i, set, |=))
#define CPU_CLR(i, set) ((void)__CPU_op(i, set, &= ~))
#define CPU_ISSET(i, set) (!!__CPU_op(i, set, &))
#define CPU_ZERO(set) ((void)__builtin_memset((set), 0, sizeof(cpu_set_t)))
#define CPU_COUNT(set) __sched_cpucount(sizeof(cpu_set_t), (set))

__BEGIN_DECLS
int sched_yield(void);
int sched_getcpu(void);
int sched_get_priority_max(int);
int sched_get_priority_min(int);
int sched_getscheduler(pid_t);
int sched_setscheduler(pid_t, int, const struct sched_param *);
int sched_getparam(pid_t, struct sched_param *);
int sched_setparam(pid_t, const struct sched_param *);
int sched_rr_get_interval(pid_t, struct timespec *);
int sched_getaffinity(pid_t, size_t, cpu_set_t *);
int sched_setaffinity(pid_t, size_t, const cpu_set_t *);
int __sched_cpucount(size_t, const cpu_set_t *);
__END_DECLS

#endif
