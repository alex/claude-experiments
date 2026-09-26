// pthread_cancel: deferred delivery at a blocking call, cleanup handlers,
// disabled state, asynchronous mode, pthread_testcancel, and the reserved
// signal staying unblockable.
#include <errno.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

static int pipefd[2];
static volatile int cleaned, spins, reached;

static void cleanup(void *arg) { cleaned = (int)(long)arg; }

static void *blocked(void *arg) {
    (void)arg;
    pthread_cleanup_push(cleanup, (void *)7);
    char c;
    read(pipefd[0], &c, 1); // never returns
    reached = 1;
    pthread_cleanup_pop(0);
    return NULL;
}

static void *disabled_then_enabled(void *arg) {
    (void)arg;
    int old;
    pthread_setcancelstate(PTHREAD_CANCEL_DISABLE, &old);
    if (old != PTHREAD_CANCEL_ENABLE) return (void *)1;
    struct timespec ts = {0, 100 * 1000 * 1000};
    nanosleep(&ts, NULL); // the request arrives meanwhile and must wait
    reached = 2;
    pthread_setcancelstate(PTHREAD_CANCEL_ENABLE, NULL);
    pthread_testcancel(); // acted on here
    reached = 3;
    return NULL;
}

static void *spinning(void *arg) {
    (void)arg;
    pthread_setcanceltype(PTHREAD_CANCEL_ASYNCHRONOUS, NULL);
    for (;;) spins++;
    return NULL;
}

static void *masked(void *arg) {
    (void)arg;
    sigset_t all;
    sigfillset(&all);
    pthread_sigmask(SIG_BLOCK, &all, NULL); // must not block the cancel signal
    for (;;) sleep(1);
    return NULL;
}

int main(void) {
    CHECK(pipe(pipefd) == 0);
    pthread_t t;
    void *res;

    CHECK(pthread_create(&t, NULL, blocked, NULL) == 0);
    struct timespec ts = {0, 50 * 1000 * 1000};
    nanosleep(&ts, NULL);
    CHECK(pthread_cancel(t) == 0);
    CHECK(pthread_join(t, &res) == 0 && res == PTHREAD_CANCELED);
    CHECK(cleaned == 7 && reached == 0);

    CHECK(pthread_create(&t, NULL, disabled_then_enabled, NULL) == 0);
    nanosleep(&ts, NULL);
    CHECK(pthread_cancel(t) == 0);
    CHECK(pthread_join(t, &res) == 0 && res == PTHREAD_CANCELED);
    CHECK(reached == 2);

    CHECK(pthread_create(&t, NULL, spinning, NULL) == 0);
    nanosleep(&ts, NULL);
    CHECK(pthread_cancel(t) == 0);
    CHECK(pthread_join(t, &res) == 0 && res == PTHREAD_CANCELED);
    CHECK(spins > 0);

    CHECK(pthread_create(&t, NULL, masked, NULL) == 0);
    nanosleep(&ts, NULL);
    CHECK(pthread_cancel(t) == 0);
    CHECK(pthread_join(t, &res) == 0 && res == PTHREAD_CANCELED);

    // The reserved signals cannot get user handlers.
    CHECK(signal(33, SIG_IGN) == SIG_ERR && errno == EINVAL);
    // Cancelling a finished thread is harmless.
    CHECK(pthread_setcanceltype(PTHREAD_CANCEL_DEFERRED, NULL) == 0);
    CHECK(pthread_setcancelstate(42, NULL) == EINVAL);
    return 0;
}
