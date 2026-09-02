#ifndef _PTHREAD_H
#define _PTHREAD_H
#include <bits/features.h>

#define __NEED_size_t
#define __NEED_struct_timespec
#define __NEED_time_t
#define __NEED_clockid_t
#define __NEED_sigset_t
#include <bits/alltypes.h>
#include <sched.h>
#include <time.h>

typedef unsigned long pthread_t;
typedef int pthread_key_t;
typedef int pthread_once_t;
typedef int pthread_spinlock_t;
typedef struct { unsigned __s[4]; } pthread_mutex_t;
typedef struct { unsigned __s[4]; } pthread_cond_t;
typedef struct { unsigned __s[4]; } pthread_rwlock_t;
typedef struct { unsigned __s[4]; } pthread_barrier_t;
typedef struct { unsigned __type; } pthread_mutexattr_t;
typedef struct { unsigned __clock; } pthread_condattr_t;
typedef struct { unsigned __x; } pthread_rwlockattr_t;
typedef struct { unsigned __x; } pthread_barrierattr_t;
typedef struct {
    size_t __stack_size;
    size_t __guard_size;
    void *__stack_addr;
    int __detached;
    int __pad;
} pthread_attr_t;

#define PTHREAD_MUTEX_INITIALIZER {{0, 0, 0, 0}}
#define PTHREAD_RECURSIVE_MUTEX_INITIALIZER_NP {{0, 1, 0, 0}}
#define PTHREAD_ERRORCHECK_MUTEX_INITIALIZER_NP {{0, 2, 0, 0}}
#define PTHREAD_COND_INITIALIZER {{0, 0, 0, 0}}
#define PTHREAD_RWLOCK_INITIALIZER {{0, 0, 0, 0}}
#define PTHREAD_ONCE_INIT 0

#define PTHREAD_CREATE_JOINABLE 0
#define PTHREAD_CREATE_DETACHED 1
#define PTHREAD_MUTEX_NORMAL 0
#define PTHREAD_MUTEX_DEFAULT 0
#define PTHREAD_MUTEX_RECURSIVE 1
#define PTHREAD_MUTEX_ERRORCHECK 2
#define PTHREAD_PROCESS_PRIVATE 0
#define PTHREAD_PROCESS_SHARED 1
#define PTHREAD_BARRIER_SERIAL_THREAD (-1)
#define PTHREAD_CANCEL_ENABLE 0
#define PTHREAD_CANCEL_DISABLE 1
#define PTHREAD_CANCEL_DEFERRED 0
#define PTHREAD_CANCEL_ASYNCHRONOUS 1

#define PTHREAD_CANCEL_ENABLE 0
#define PTHREAD_CANCEL_DISABLE 1
#define PTHREAD_CANCEL_DEFERRED 0
#define PTHREAD_CANCEL_ASYNCHRONOUS 1
#define PTHREAD_CANCELED ((void *)-1)

__BEGIN_DECLS

int pthread_create(pthread_t *__RESTRICT, const pthread_attr_t *__RESTRICT, void *(*)(void *), void *__RESTRICT);
int pthread_join(pthread_t, void **);
int pthread_tryjoin_np(pthread_t, void **);
int pthread_detach(pthread_t);
__NORETURN void pthread_exit(void *);
pthread_t pthread_self(void);
int pthread_equal(pthread_t, pthread_t);
int pthread_sigmask(int, const sigset_t *__RESTRICT, sigset_t *__RESTRICT);
int pthread_kill(pthread_t, int);
int pthread_cancel(pthread_t);
int pthread_setcancelstate(int, int *);
int pthread_setcanceltype(int, int *);
void pthread_testcancel(void);
int pthread_setname_np(pthread_t, const char *);
int pthread_atfork(void (*)(void), void (*)(void), void (*)(void));

int pthread_attr_init(pthread_attr_t *);
int pthread_attr_destroy(pthread_attr_t *);
int pthread_attr_setdetachstate(pthread_attr_t *, int);
int pthread_attr_getdetachstate(const pthread_attr_t *, int *);
int pthread_attr_setstacksize(pthread_attr_t *, size_t);
int pthread_attr_getstacksize(const pthread_attr_t *__RESTRICT, size_t *__RESTRICT);
int pthread_attr_setguardsize(pthread_attr_t *, size_t);
int pthread_attr_getguardsize(const pthread_attr_t *__RESTRICT, size_t *__RESTRICT);

int pthread_mutex_init(pthread_mutex_t *__RESTRICT, const pthread_mutexattr_t *__RESTRICT);
int pthread_mutex_destroy(pthread_mutex_t *);
int pthread_mutex_lock(pthread_mutex_t *);
int pthread_mutex_trylock(pthread_mutex_t *);
int pthread_mutex_timedlock(pthread_mutex_t *__RESTRICT, const struct timespec *__RESTRICT);
int pthread_mutex_clocklock(pthread_mutex_t *__RESTRICT, clockid_t, const struct timespec *__RESTRICT);
int pthread_mutex_unlock(pthread_mutex_t *);
int pthread_mutexattr_init(pthread_mutexattr_t *);
int pthread_mutexattr_destroy(pthread_mutexattr_t *);
int pthread_mutexattr_settype(pthread_mutexattr_t *, int);
int pthread_mutexattr_gettype(const pthread_mutexattr_t *__RESTRICT, int *__RESTRICT);
int pthread_mutexattr_setpshared(pthread_mutexattr_t *, int);

int pthread_cond_init(pthread_cond_t *__RESTRICT, const pthread_condattr_t *__RESTRICT);
int pthread_cond_destroy(pthread_cond_t *);
int pthread_cond_wait(pthread_cond_t *__RESTRICT, pthread_mutex_t *__RESTRICT);
int pthread_cond_timedwait(pthread_cond_t *__RESTRICT, pthread_mutex_t *__RESTRICT, const struct timespec *__RESTRICT);
int pthread_cond_clockwait(pthread_cond_t *__RESTRICT, pthread_mutex_t *__RESTRICT, clockid_t, const struct timespec *__RESTRICT);
int pthread_cond_signal(pthread_cond_t *);
int pthread_cond_broadcast(pthread_cond_t *);
int pthread_condattr_init(pthread_condattr_t *);
int pthread_condattr_destroy(pthread_condattr_t *);
int pthread_condattr_setclock(pthread_condattr_t *, clockid_t);
int pthread_condattr_getclock(const pthread_condattr_t *__RESTRICT, clockid_t *__RESTRICT);
int pthread_condattr_setpshared(pthread_condattr_t *, int);

int pthread_rwlock_init(pthread_rwlock_t *__RESTRICT, const pthread_rwlockattr_t *__RESTRICT);
int pthread_rwlock_destroy(pthread_rwlock_t *);
int pthread_rwlock_rdlock(pthread_rwlock_t *);
int pthread_rwlock_tryrdlock(pthread_rwlock_t *);
int pthread_rwlock_timedrdlock(pthread_rwlock_t *__RESTRICT, const struct timespec *__RESTRICT);
int pthread_rwlock_wrlock(pthread_rwlock_t *);
int pthread_rwlock_trywrlock(pthread_rwlock_t *);
int pthread_rwlock_timedwrlock(pthread_rwlock_t *__RESTRICT, const struct timespec *__RESTRICT);
int pthread_rwlock_unlock(pthread_rwlock_t *);
int pthread_rwlockattr_init(pthread_rwlockattr_t *);
int pthread_rwlockattr_destroy(pthread_rwlockattr_t *);

int pthread_spin_init(pthread_spinlock_t *, int);
int pthread_spin_destroy(pthread_spinlock_t *);
int pthread_spin_lock(pthread_spinlock_t *);
int pthread_spin_trylock(pthread_spinlock_t *);
int pthread_spin_unlock(pthread_spinlock_t *);

int pthread_barrier_init(pthread_barrier_t *__RESTRICT, const pthread_barrierattr_t *__RESTRICT, unsigned);
int pthread_barrier_destroy(pthread_barrier_t *);
int pthread_barrier_wait(pthread_barrier_t *);

int pthread_once(pthread_once_t *, void (*)(void));

int pthread_key_create(pthread_key_t *, void (*)(void *));
int pthread_key_delete(pthread_key_t);
void *pthread_getspecific(pthread_key_t);
int pthread_setspecific(pthread_key_t, const void *);

struct __ptcb {
    void (*__f)(void *);
    void *__x;
    struct __ptcb *__next;
};
void _pthread_cleanup_push(struct __ptcb *, void (*)(void *), void *);
void _pthread_cleanup_pop(struct __ptcb *, int);
#define pthread_cleanup_push(f, x) do { struct __ptcb __cb; _pthread_cleanup_push(&__cb, f, x);
#define pthread_cleanup_pop(r) _pthread_cleanup_pop(&__cb, (r)); } while (0)

__END_DECLS

#endif
