#ifndef _SCHED_H
#define _SCHED_H
#include <bits/features.h>

#define __NEED_pid_t
#define __NEED_time_t
#define __NEED_struct_timespec
#include <bits/alltypes.h>

struct sched_param { int sched_priority; };

#define SCHED_OTHER 0
#define SCHED_FIFO 1
#define SCHED_RR 2

__BEGIN_DECLS
int sched_yield(void);
__END_DECLS

#endif
