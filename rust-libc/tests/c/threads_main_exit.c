// pthread_exit from main lets the other threads finish; the process
// then exits with status 0 (as if by exit(0)), running atexit handlers.
#include <pthread.h>
#include <stdlib.h>
#include <unistd.h>

static void at_exit(void) { _exit(9); }
// expect-exit: 9

static void *worker(void *arg) {
    (void)arg;
    struct timespec ts = {0, 20000000};
    nanosleep(&ts, NULL);
    return NULL;
}

int main(void) {
    atexit(at_exit);
    pthread_t t;
    if (pthread_create(&t, NULL, worker, NULL) != 0) _exit(1);
    pthread_exit(NULL);
}
