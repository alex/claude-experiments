// pthreads: creation, join, detach, mutexes, condvars, rwlocks, barriers,
// once, keys, cleanup handlers, semaphores and per-thread TLS.
#include <errno.h>
#include <pthread.h>
#include <semaphore.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); _exit(__LINE__); } } while (0)

static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t cond = PTHREAD_COND_INITIALIZER;
static pthread_rwlock_t rwlock = PTHREAD_RWLOCK_INITIALIZER;
static pthread_barrier_t barrier;
static pthread_once_t once = PTHREAD_ONCE_INIT;
static pthread_key_t key;
static sem_t sem;
static __thread int tls_counter = 5;
static long counter;
static int once_calls;
static int dtor_calls;
static int cleanup_calls;
static int queue;

static void init_once(void) { once_calls++; }
static void key_dtor(void *p) { (void)p; __sync_fetch_and_add(&dtor_calls, 1); }
static void cleanup(void *p) { (void)p; __sync_fetch_and_add(&cleanup_calls, 1); }

static void *worker(void *arg) {
    long id = (long)arg;
    pthread_once(&once, init_once);
    CHECK(tls_counter == 5);
    tls_counter += (int)id;
    CHECK(pthread_setspecific(key, &tls_counter) == 0);
    for (int i = 0; i < 10000; i++) {
        pthread_mutex_lock(&mutex);
        counter++;
        pthread_mutex_unlock(&mutex);
        pthread_rwlock_rdlock(&rwlock);
        CHECK(counter >= 0);
        pthread_rwlock_unlock(&rwlock);
        if (i % 100 == 0) {
            pthread_rwlock_wrlock(&rwlock);
            counter += 0;
            pthread_rwlock_unlock(&rwlock);
        }
    }
    pthread_barrier_wait(&barrier);
    CHECK(tls_counter == 5 + id);
    CHECK(pthread_getspecific(key) == &tls_counter);
    pthread_cleanup_push(cleanup, NULL);
    pthread_cleanup_pop(1);
    return (void *)(id * 10);
}

static void *consumer(void *arg) {
    (void)arg;
    long got = 0;
    for (int i = 0; i < 100; i++) {
        pthread_mutex_lock(&mutex);
        while (queue == 0) pthread_cond_wait(&cond, &mutex);
        queue--;
        got++;
        pthread_mutex_unlock(&mutex);
    }
    return (void *)got;
}

static void *exiter(void *arg) {
    (void)arg;
    pthread_cleanup_push(cleanup, NULL);
    pthread_exit((void *)42);
    pthread_cleanup_pop(0);
    return NULL;
}

static void *detached(void *arg) {
    sem_post((sem_t *)arg);
    return NULL;
}

int main(void) {
    CHECK(pthread_key_create(&key, key_dtor) == 0);
    CHECK(pthread_barrier_init(&barrier, NULL, 4) == 0);
    CHECK(sem_init(&sem, 0, 0) == 0);

    pthread_t t[4];
    for (long i = 0; i < 4; i++) CHECK(pthread_create(&t[i], NULL, worker, (void *)i) == 0);
    for (long i = 0; i < 4; i++) {
        void *ret;
        CHECK(pthread_join(t[i], &ret) == 0);
        CHECK((long)ret == i * 10);
    }
    CHECK(counter == 40000);
    CHECK(once_calls == 1);
    CHECK(dtor_calls == 4);
    CHECK(cleanup_calls == 4);
    CHECK(tls_counter == 5);

    // Producer / consumer through a condition variable.
    pthread_t c;
    CHECK(pthread_create(&c, NULL, consumer, NULL) == 0);
    for (int i = 0; i < 100; i++) {
        pthread_mutex_lock(&mutex);
        queue++;
        pthread_cond_signal(&cond);
        pthread_mutex_unlock(&mutex);
    }
    void *got;
    CHECK(pthread_join(c, &got) == 0 && (long)got == 100);

    // pthread_exit with a pending cleanup handler.
    pthread_t e;
    CHECK(pthread_create(&e, NULL, exiter, NULL) == 0);
    CHECK(pthread_join(e, &got) == 0 && (long)got == 42);
    CHECK(cleanup_calls == 5);

    // Detached threads signal through a semaphore.
    pthread_attr_t attr;
    CHECK(pthread_attr_init(&attr) == 0);
    CHECK(pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED) == 0);
    CHECK(pthread_attr_setstacksize(&attr, 256 * 1024) == 0);
    for (int i = 0; i < 20; i++) {
        pthread_t d;
        CHECK(pthread_create(&d, &attr, detached, &sem) == 0);
    }
    for (int i = 0; i < 20; i++) CHECK(sem_wait(&sem) == 0);
    CHECK(sem_trywait(&sem) == -1 && errno == EAGAIN);
    // Detach after creation, joining a detached thread fails.
    pthread_t d;
    CHECK(pthread_create(&d, NULL, detached, &sem) == 0);
    CHECK(pthread_detach(d) == 0);
    CHECK(sem_wait(&sem) == 0);

    // Recursive and error-checking mutexes.
    pthread_mutexattr_t ma;
    pthread_mutex_t rm;
    CHECK(pthread_mutexattr_init(&ma) == 0);
    CHECK(pthread_mutexattr_settype(&ma, PTHREAD_MUTEX_RECURSIVE) == 0);
    CHECK(pthread_mutex_init(&rm, &ma) == 0);
    CHECK(pthread_mutex_lock(&rm) == 0 && pthread_mutex_lock(&rm) == 0);
    CHECK(pthread_mutex_unlock(&rm) == 0 && pthread_mutex_unlock(&rm) == 0);
    CHECK(pthread_mutex_unlock(&rm) == EPERM);
    CHECK(pthread_mutexattr_settype(&ma, PTHREAD_MUTEX_ERRORCHECK) == 0);
    CHECK(pthread_mutex_init(&rm, &ma) == 0);
    CHECK(pthread_mutex_lock(&rm) == 0 && pthread_mutex_lock(&rm) == EDEADLK);
    CHECK(pthread_mutex_unlock(&rm) == 0);

    // Timed waits that time out.
    struct timespec ts;
    CHECK(clock_gettime(CLOCK_REALTIME, &ts) == 0);
    ts.tv_nsec += 5000000;
    if (ts.tv_nsec >= 1000000000) { ts.tv_sec++; ts.tv_nsec -= 1000000000; }
    pthread_mutex_lock(&mutex);
    CHECK(pthread_cond_timedwait(&cond, &mutex, &ts) == ETIMEDOUT);
    pthread_mutex_unlock(&mutex);
    CHECK(sem_timedwait(&sem, &ts) == -1 && errno == ETIMEDOUT);

    pthread_spinlock_t spin;
    CHECK(pthread_spin_init(&spin, 0) == 0);
    CHECK(pthread_spin_lock(&spin) == 0 && pthread_spin_trylock(&spin) == EBUSY);
    CHECK(pthread_spin_unlock(&spin) == 0);

    CHECK(pthread_self() != 0 && pthread_equal(pthread_self(), pthread_self()));
    CHECK(pthread_join(pthread_self(), NULL) == EDEADLK);
    CHECK(pthread_setname_np(pthread_self(), "tester") == 0);
    return 0;
}
