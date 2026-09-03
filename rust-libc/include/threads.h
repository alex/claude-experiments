#ifndef _THREADS_H
#define _THREADS_H
#include <bits/features.h>
#include <pthread.h>
#include <time.h>

typedef pthread_t thrd_t;
typedef pthread_mutex_t mtx_t;
typedef pthread_cond_t cnd_t;
typedef pthread_key_t tss_t;
typedef pthread_once_t once_flag;
typedef int (*thrd_start_t)(void *);
typedef void (*tss_dtor_t)(void *);

#define ONCE_FLAG_INIT 0
#define TSS_DTOR_ITERATIONS 4
#define thread_local _Thread_local

enum { thrd_success = 0, thrd_busy = 1, thrd_error = 2, thrd_nomem = 3, thrd_timedout = 4 };
enum { mtx_plain = 0, mtx_timed = 1, mtx_recursive = 2 };

__BEGIN_DECLS
int thrd_create(thrd_t *, thrd_start_t, void *);
int thrd_join(thrd_t, int *);
int thrd_detach(thrd_t);
thrd_t thrd_current(void);
int thrd_equal(thrd_t, thrd_t);
__NORETURN void thrd_exit(int);
void thrd_yield(void);
int thrd_sleep(const struct timespec *, struct timespec *);
int mtx_init(mtx_t *, int);
void mtx_destroy(mtx_t *);
int mtx_lock(mtx_t *);
int mtx_trylock(mtx_t *);
int mtx_timedlock(mtx_t *__RESTRICT, const struct timespec *__RESTRICT);
int mtx_unlock(mtx_t *);
int cnd_init(cnd_t *);
void cnd_destroy(cnd_t *);
int cnd_signal(cnd_t *);
int cnd_broadcast(cnd_t *);
int cnd_wait(cnd_t *, mtx_t *);
int cnd_timedwait(cnd_t *__RESTRICT, mtx_t *__RESTRICT, const struct timespec *__RESTRICT);
int tss_create(tss_t *, tss_dtor_t);
void tss_delete(tss_t);
void *tss_get(tss_t);
int tss_set(tss_t, void *);
void call_once(once_flag *, void (*)(void));
__END_DECLS

#endif
