#ifndef _SEMAPHORE_H
#define _SEMAPHORE_H
#include <bits/features.h>

#define __NEED_struct_timespec
#define __NEED_time_t
#include <bits/alltypes.h>

typedef struct { unsigned __s[4]; } sem_t;

#define SEM_FAILED ((sem_t *)0)
#define SEM_VALUE_MAX 0x7fffffff

__BEGIN_DECLS

int sem_init(sem_t *, int, unsigned);
int sem_destroy(sem_t *);
int sem_wait(sem_t *);
int sem_trywait(sem_t *);
int sem_timedwait(sem_t *__RESTRICT, const struct timespec *__RESTRICT);
int sem_post(sem_t *);
int sem_getvalue(sem_t *__RESTRICT, int *__RESTRICT);

__END_DECLS

#endif
