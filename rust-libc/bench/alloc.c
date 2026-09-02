// Allocator workloads modelled on real programs, run by `cargo xtask bench
// alloc` against rustlibc and glibc. Output lines are "name<TAB>value<TAB>unit".
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static void report_ns(const char *name, double secs, double ops) {
    printf("%s\t%.1f\tns/op\n", name, secs / ops * 1e9);
}

static inline uint64_t rnd(uint64_t *s) {
    uint64_t x = *s;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    return *s = x;
}

static long rss_kb(void) {
    FILE *f = fopen("/proc/self/statm", "r");
    long size = 0, resident = 0;
    if (f) {
        if (fscanf(f, "%ld %ld", &size, &resident) != 2) resident = 0;
        fclose(f);
    }
    return resident * (long)sysconf(_SC_PAGESIZE) / 1024;
}

// A live set of `slots` blocks; each operation frees a random slot and
// allocates a new block of a random size in [lo, hi], touching it.
static double live_set(size_t slots, size_t lo, size_t hi, long ops, uint64_t *s) {
    void **set = calloc(slots, sizeof *set);
    for (size_t i = 0; i < slots; i++) {
        size_t n = lo + rnd(s) % (hi - lo + 1);
        set[i] = malloc(n);
        memset(set[i], 1, n);
    }
    double t0 = now();
    for (long i = 0; i < ops; i++) {
        size_t k = rnd(s) % slots;
        free(set[k]);
        size_t n = lo + rnd(s) % (hi - lo + 1);
        set[k] = malloc(n);
        ((char *)set[k])[0] = 1;
        ((char *)set[k])[n - 1] = 2;
    }
    double t = now() - t0;
    for (size_t i = 0; i < slots; i++) free(set[i]);
    free(set);
    return t;
}

// larson: every thread works on its own live set (allocator scalability).
struct larson_arg { long ops; double secs; uint64_t seed; };
static void *larson_thread(void *p) {
    struct larson_arg *a = p;
    uint64_t s = a->seed;
    a->secs = live_set(1024, 8, 1000, a->ops, &s);
    return NULL;
}

// Producer/consumer: producers allocate and hand blocks to consumers over a
// bounded ring, consumers free them (every block is freed by a foreign
// thread).
#define RING 1024
static void *ring[RING];
static pthread_mutex_t ring_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t ring_cv = PTHREAD_COND_INITIALIZER;
static size_t ring_head, ring_tail;
static long ring_left;

static void *producer(void *p) {
    long n = (long)p;
    uint64_t s = 42;
    for (long i = 0; i < n; i++) {
        size_t sz = 16 + rnd(&s) % 500;
        void *b = malloc(sz);
        memset(b, 3, sz);
        pthread_mutex_lock(&ring_mu);
        while (ring_head - ring_tail == RING) pthread_cond_wait(&ring_cv, &ring_mu);
        ring[ring_head++ % RING] = b;
        pthread_cond_broadcast(&ring_cv);
        pthread_mutex_unlock(&ring_mu);
    }
    return NULL;
}

static void *consumer(void *p) {
    (void)p;
    for (;;) {
        pthread_mutex_lock(&ring_mu);
        while (ring_head == ring_tail && ring_left > 0) pthread_cond_wait(&ring_cv, &ring_mu);
        if (ring_head == ring_tail) {
            pthread_mutex_unlock(&ring_mu);
            return NULL;
        }
        void *b = ring[ring_tail++ % RING];
        ring_left--;
        pthread_cond_broadcast(&ring_cv);
        pthread_mutex_unlock(&ring_mu);
        free(b);
    }
}

int main(int argc, char **argv) {
    (void)argc; (void)argv;
    uint64_t s = 0x9e3779b97f4a7c15ull;
    double t;

    t = live_set(4096, 16, 256, 4000000, &s);
    report_ns("alloc small mixed 16-256", t, 4000000);
    t = live_set(2048, 256, 8192, 1000000, &s);
    report_ns("alloc medium 256-8K", t, 1000000);
    t = live_set(64, 65536, 1 << 20, 20000, &s);
    report_ns("alloc large 64K-1M", t, 20000);

    // String-builder growth: realloc doubling from 16 bytes to 1 MiB.
    double t0 = now();
    for (int r = 0; r < 200; r++) {
        char *b = malloc(16);
        size_t cap = 16, len = 0;
        while (cap < (1 << 20)) {
            memset(b + len, 'x', cap - len);
            len = cap;
            cap *= 2;
            b = realloc(b, cap);
        }
        free(b);
    }
    report_ns("realloc growth 16->1M", now() - t0, 200.0 * 17);

    // Many small objects freed in allocation order (a parser building and
    // tearing down a tree).
    enum { N = 200000 };
    void **objs = malloc(N * sizeof *objs);
    t0 = now();
    for (int r = 0; r < 10; r++) {
        for (int i = 0; i < N; i++) objs[i] = malloc(24 + (i % 5) * 16);
        for (int i = 0; i < N; i++) free(objs[i]);
    }
    report_ns("tree build/teardown 24-88", now() - t0, 10.0 * N * 2);
    // ... and in reverse order.
    t0 = now();
    for (int r = 0; r < 10; r++) {
        for (int i = 0; i < N; i++) objs[i] = malloc(24 + (i % 5) * 16);
        for (int i = N - 1; i >= 0; i--) free(objs[i]);
    }
    report_ns("tree build/teardown reversed", now() - t0, 10.0 * N * 2);
    free(objs);

    // larson: 4 threads, private live sets.
    {
        pthread_t th[4];
        struct larson_arg args[4];
        for (int i = 0; i < 4; i++) {
            args[i].ops = 1000000;
            args[i].seed = 1000 + i;
            pthread_create(&th[i], NULL, larson_thread, &args[i]);
        }
        double total = 0;
        for (int i = 0; i < 4; i++) {
            pthread_join(th[i], NULL);
            total += args[i].secs;
        }
        report_ns("larson 4 threads (per op)", total / 4, 1000000);
    }

    // Producer/consumer: 2 producers, 2 consumers, 400k blocks.
    {
        ring_left = 400000;
        pthread_t pr[2], co[2];
        t0 = now();
        for (int i = 0; i < 2; i++) pthread_create(&co[i], NULL, consumer, NULL);
        for (int i = 0; i < 2; i++) pthread_create(&pr[i], NULL, producer, (void *)200000L);
        for (int i = 0; i < 2; i++) pthread_join(pr[i], NULL);
        for (int i = 0; i < 2; i++) pthread_join(co[i], NULL);
        report_ns("producer/consumer (per block)", now() - t0, 400000);
    }

    // Fragmentation: 100 MiB of small blocks, free 90% at random, then
    // allocate 30 MiB of 2 KiB blocks; report resident memory.
    {
        enum { M = 1600000 };
        void **blocks = malloc(M * sizeof *blocks);
        for (int i = 0; i < M; i++) {
            blocks[i] = malloc(64);
            memset(blocks[i], 5, 64);
        }
        for (int i = 0; i < M; i++) {
            if (rnd(&s) % 10 != 0) {
                free(blocks[i]);
                blocks[i] = NULL;
            }
        }
        long after_free = rss_kb();
        void **mid = malloc(15360 * sizeof *mid);
        for (int i = 0; i < 15360; i++) {
            mid[i] = malloc(2048);
            memset(mid[i], 6, 2048);
        }
        printf("fragmentation RSS after 90%% free\t%ld\tKB\n", after_free);
        printf("fragmentation RSS after refill\t%ld\tKB\n", rss_kb());
        for (int i = 0; i < 15360; i++) free(mid[i]);
        for (int i = 0; i < M; i++) free(blocks[i]);
        free(blocks);
        free(mid);
        printf("fragmentation RSS after all freed\t%ld\tKB\n", rss_kb());
    }
    return 0;
}
