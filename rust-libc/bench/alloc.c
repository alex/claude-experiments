// Allocator workloads modelled on real programs and on the classic
// allocator benchmarks (larson, xmalloc-test, cache-scratch/thrash,
// mstress, sh6bench, alloc-test, malloc-large, glibc-simple), run by
// `cargo xtask bench alloc` against rustlibc, glibc and, when installed,
// mimalloc, jemalloc and tcmalloc.
//
// Every timed workload runs RUNS times and reports the best run, which is
// the least noisy statistic on a shared machine. Output lines are
// "name<TAB>value<TAB>unit"; an optional argument selects workloads whose
// name contains it.
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#ifndef RUNS
#define RUNS 3
#endif

static const char *filter;

static int selected(const char *name) {
    return !filter || strstr(name, filter) != NULL;
}

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static void report_ns(const char *name, double secs, double ops) {
    printf("%s\t%.2f\tns/op\n", name, secs / ops * 1e9);
    fflush(stdout);
}

static void report_kb(const char *name, long kb) {
    printf("%s\t%ld\tKB\n", name, kb);
    fflush(stdout);
}

static inline uint64_t rnd(uint64_t *s) {
    uint64_t x = *s;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    return *s = x;
}

// Geometric-ish size distribution: mostly small, with a long tail up to
// `max`, the shape of most programs' allocation sizes.
static size_t tail_size(uint64_t *s, size_t max) {
    uint64_t r = rnd(s);
    unsigned shift = (unsigned)(r % 64);
    size_t n = 8 + (size_t)((r >> 8) % (16u << (shift % 12)));
    return n > max ? max : n;
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

#define BEST(var, body) do { \
    double best_ = 1e30; \
    for (int run_ = 0; run_ < RUNS; run_++) { double t_; body; if (t_ < best_) best_ = t_; } \
    var = best_; } while (0)

// ---------------------------------------------------------------------
// Single-threaded workloads.

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

// malloc+free of one block, the tightest loop there is.
static double pair(size_t size, long ops) {
    double t0 = now();
    for (long i = 0; i < ops; i++) {
        void *p = malloc(size);
        ((volatile char *)p)[0] = 1;
        free(p);
    }
    return now() - t0;
}

// cfrac/espresso style: bursts of small short-lived objects freed in
// LIFO order, some kept for longer.
static double cfrac(long ops, uint64_t *s) {
    enum { STACK = 512, KEEP = 4096 };
    void *stack[STACK];
    void **keep = calloc(KEEP, sizeof *keep);
    size_t kept = 0;
    double t0 = now();
    for (long i = 0; i < ops;) {
        size_t depth = 1 + rnd(s) % STACK;
        for (size_t d = 0; d < depth; d++) {
            size_t n = 8 + rnd(s) % 56;
            stack[d] = malloc(n);
            ((char *)stack[d])[0] = (char)d;
        }
        // Every 16th block survives the burst.
        for (size_t d = depth; d-- > 0;) {
            if ((d & 15) == 15 && kept < KEEP) {
                keep[kept++] = stack[d];
            } else {
                free(stack[d]);
            }
        }
        if (kept == KEEP) {
            for (size_t k = 0; k < KEEP; k++) free(keep[k]);
            kept = 0;
        }
        i += (long)depth;
    }
    double t = now() - t0;
    for (size_t k = 0; k < kept; k++) free(keep[k]);
    free(keep);
    return t;
}

// alloc-test: a large live set with a long-tailed size distribution
// (up to 64 KiB), random replacement.
static double alloc_test(size_t slots, long ops, uint64_t *s) {
    void **set = calloc(slots, sizeof *set);
    size_t *sz = calloc(slots, sizeof *sz);
    double t0 = now();
    for (long i = 0; i < ops; i++) {
        size_t k = rnd(s) % slots;
        if (set[k]) free(set[k]);
        sz[k] = tail_size(s, 64 << 10);
        set[k] = malloc(sz[k]);
        memset(set[k], 1, sz[k] < 64 ? sz[k] : 64);
    }
    double t = now() - t0;
    for (size_t i = 0; i < slots; i++) free(set[i]);
    free(set);
    free(sz);
    return t;
}

// sh6bench: for each size class, allocate a batch, touch it, free half
// of it at random, refill, then free everything.
static double sh6bench(uint64_t *s) {
    enum { N = 2000 };
    void *blocks[N];
    double t0 = now();
    for (size_t size = 8; size <= 8192; size = size * 3 / 2 + 8) {
        for (int rep = 0; rep < 4; rep++) {
            for (int i = 0; i < N; i++) {
                blocks[i] = malloc(size);
                memset(blocks[i], 1, size < 32 ? size : 32);
            }
            for (int i = 0; i < N; i++) {
                if (rnd(s) & 1) {
                    free(blocks[i]);
                    blocks[i] = NULL;
                }
            }
            for (int i = 0; i < N; i++) {
                if (!blocks[i]) blocks[i] = malloc(size);
            }
            for (int i = 0; i < N; i++) free(blocks[i]);
        }
    }
    return now() - t0;
}

// glibc-simple: allocate, keep a third, free the rest, repeatedly.
static double glibc_simple(long rounds, uint64_t *s) {
    enum { N = 1000 };
    void *keep[N];
    size_t kept = 0;
    double t0 = now();
    for (long r = 0; r < rounds; r++) {
        for (int i = 0; i < N; i++) {
            void *p = malloc(8 + rnd(s) % 500);
            ((char *)p)[0] = 1;
            if (i % 3 == 0 && kept < N) keep[kept++] = p; else free(p);
        }
        if (kept >= N / 2) {
            for (size_t k = 0; k < kept; k++) free(keep[k]);
            kept = 0;
        }
    }
    double t = now() - t0;
    for (size_t k = 0; k < kept; k++) free(keep[k]);
    return t;
}

// malloc-large: 1-16 MiB blocks with a small live set, touched.
static double malloc_large(long ops, uint64_t *s) {
    enum { SLOTS = 8 };
    void *set[SLOTS] = {0};
    double t0 = now();
    for (long i = 0; i < ops; i++) {
        size_t k = rnd(s) % SLOTS;
        free(set[k]);
        size_t n = (1u << 20) + rnd(s) % (15u << 20);
        set[k] = malloc(n);
        // Touch every 16th page.
        for (size_t off = 0; off < n; off += 16 * 4096) ((char *)set[k])[off] = 1;
    }
    double t = now() - t0;
    for (int k = 0; k < SLOTS; k++) free(set[k]);
    return t;
}

static double calloc_small(long ops) {
    enum { N = 1024 };
    void *blocks[N];
    double t0 = now();
    for (long r = 0; r < ops / N; r++) {
        for (int i = 0; i < N; i++) {
            blocks[i] = calloc(1, 64);
            ((char *)blocks[i])[8] = 1;
        }
        for (int i = 0; i < N; i++) free(blocks[i]);
    }
    return now() - t0;
}

static double calloc_medium(long ops) {
    enum { N = 64 };
    void *blocks[N];
    double t0 = now();
    for (long r = 0; r < ops / N; r++) {
        for (int i = 0; i < N; i++) {
            blocks[i] = calloc(1, 64 << 10);
            ((char *)blocks[i])[4096] = 1;
        }
        for (int i = 0; i < N; i++) free(blocks[i]);
    }
    return now() - t0;
}

static double memalign_small(long ops) {
    enum { N = 512 };
    void *blocks[N];
    double t0 = now();
    for (long r = 0; r < ops / N; r++) {
        for (int i = 0; i < N; i++) {
            if (posix_memalign(&blocks[i], 64, 100) != 0) abort();
            ((char *)blocks[i])[0] = 1;
        }
        for (int i = 0; i < N; i++) free(blocks[i]);
    }
    return now() - t0;
}

static double memalign_page(long ops) {
    enum { N = 64 };
    void *blocks[N];
    double t0 = now();
    for (long r = 0; r < ops / N; r++) {
        for (int i = 0; i < N; i++) {
            blocks[i] = aligned_alloc(4096, 8192);
            ((char *)blocks[i])[0] = 1;
        }
        for (int i = 0; i < N; i++) free(blocks[i]);
    }
    return now() - t0;
}

// String-builder growth: realloc doubling from 16 bytes to 1 MiB.
static double realloc_growth(long rounds) {
    double t0 = now();
    for (long r = 0; r < rounds; r++) {
        char *b = NULL;
        size_t cap = 16;
        while (cap <= (1u << 20)) {
            b = realloc(b, cap);
            b[cap - 1] = 1;
            cap *= 2;
        }
        free(b);
    }
    return now() - t0;
}

// A vector growing by 1.5x with many live siblings (the realistic case:
// in-place growth is rarely possible).
static double realloc_vectors(long ops, uint64_t *s) {
    enum { N = 256 };
    char *vec[N] = {0};
    size_t cap[N] = {0};
    double t0 = now();
    for (long i = 0; i < ops; i++) {
        size_t k = rnd(s) % N;
        if (cap[k] >= 64 << 10) {
            free(vec[k]);
            vec[k] = NULL;
            cap[k] = 0;
        }
        cap[k] = cap[k] ? cap[k] * 3 / 2 : 32;
        vec[k] = realloc(vec[k], cap[k]);
        vec[k][cap[k] - 1] = 1;
    }
    double t = now() - t0;
    for (int k = 0; k < N; k++) free(vec[k]);
    return t;
}

// Many small objects freed in allocation order (a parser building and
// tearing down a tree), and in reverse.
static double tree(int reverse) {
    enum { N = 200000 };
    void **objs = malloc(N * sizeof *objs);
    double t0 = now();
    for (int r = 0; r < 5; r++) {
        for (int i = 0; i < N; i++) objs[i] = malloc(24 + (i % 5) * 16);
        if (reverse) {
            for (int i = N - 1; i >= 0; i--) free(objs[i]);
        } else {
            for (int i = 0; i < N; i++) free(objs[i]);
        }
    }
    double t = now() - t0;
    free(objs);
    return t;
}

// ---------------------------------------------------------------------
// Multi-threaded workloads.

#define NTHREADS 4

struct larson_arg { long ops; double secs; uint64_t seed; };
static void *larson_thread(void *p) {
    struct larson_arg *a = p;
    uint64_t s = a->seed;
    a->secs = live_set(1024, 8, 1000, a->ops, &s);
    return NULL;
}

static double larson(long ops) {
    pthread_t th[NTHREADS];
    struct larson_arg args[NTHREADS];
    for (int i = 0; i < NTHREADS; i++) {
        args[i].ops = ops;
        args[i].seed = 1000 + i;
        pthread_create(&th[i], NULL, larson_thread, &args[i]);
    }
    double total = 0;
    for (int i = 0; i < NTHREADS; i++) {
        pthread_join(th[i], NULL);
        total += args[i].secs;
    }
    return total / NTHREADS;
}

// Producer/consumer over a bounded ring: every block is freed by a
// foreign thread.
#define RING 1024
static void *ring[RING];
static pthread_mutex_t ring_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t ring_cv = PTHREAD_COND_INITIALIZER;
static size_t ring_head, ring_tail;
static long ring_left;

static int ring_no_malloc;
static char ring_dummy[1024];

static void *producer(void *p) {
    long n = (long)p;
    uint64_t s = 42;
    for (long i = 0; i < n; i++) {
        size_t sz = 16 + rnd(&s) % 500;
        void *b = ring_no_malloc ? ring_dummy : malloc(sz);
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
        if (!ring_no_malloc) free(b);
    }
}

static double producer_consumer(long blocks, int no_malloc) {
    ring_no_malloc = no_malloc;
    ring_head = ring_tail = 0;
    ring_left = blocks;
    pthread_t pr[2], co[2];
    double t0 = now();
    for (int i = 0; i < 2; i++) pthread_create(&co[i], NULL, consumer, NULL);
    for (int i = 0; i < 2; i++) pthread_create(&pr[i], NULL, producer, (void *)(blocks / 2));
    for (int i = 0; i < 2; i++) pthread_join(pr[i], NULL);
    for (int i = 0; i < 2; i++) pthread_join(co[i], NULL);
    return now() - t0;
}

// xmalloc-test: each thread allocates a batch and hands it to the next
// thread in a ring, which frees it: all frees are remote, no condvars.
struct xm_arg { int id; long batches; void **mailbox; volatile int *ready; double secs; };
static void *xmalloc_thread(void *p) {
    struct xm_arg *a = p;
    enum { B = 256 };
    uint64_t s = 77 + a->id;
    int next = (a->id + 1) % NTHREADS;
    double t0 = now();
    for (long b = 0; b < a->batches; b++) {
        void **batch = malloc(B * sizeof *batch);
        for (int i = 0; i < B; i++) {
            batch[i] = malloc(16 + rnd(&s) % 240);
            ((char *)batch[i])[0] = 1;
        }
        // Hand over to the next thread (spin until its slot is free).
        while (__atomic_load_n(&a->ready[next], __ATOMIC_ACQUIRE)) sched_yield();
        a->mailbox[next] = batch;
        __atomic_store_n(&a->ready[next], 1, __ATOMIC_RELEASE);
        // Take what the previous thread left us and free it.
        while (!__atomic_load_n(&a->ready[a->id], __ATOMIC_ACQUIRE)) sched_yield();
        void **mine = a->mailbox[a->id];
        __atomic_store_n(&a->ready[a->id], 0, __ATOMIC_RELEASE);
        for (int i = 0; i < B; i++) free(mine[i]);
        free(mine);
    }
    a->secs = now() - t0;
    return NULL;
}

static double xmalloc_test(long batches) {
    pthread_t th[NTHREADS];
    struct xm_arg args[NTHREADS];
    void *mailbox[NTHREADS] = {0};
    volatile int ready[NTHREADS] = {0};
    for (int i = 0; i < NTHREADS; i++) {
        args[i].id = i;
        args[i].batches = batches;
        args[i].mailbox = mailbox;
        args[i].ready = ready;
        pthread_create(&th[i], NULL, xmalloc_thread, &args[i]);
    }
    double total = 0;
    for (int i = 0; i < NTHREADS; i++) {
        pthread_join(th[i], NULL);
        total += args[i].secs;
    }
    return total / NTHREADS;
}

// cache-scratch: objects allocated by the main thread are freed and
// reallocated by workers, which then write them repeatedly. False
// sharing between the workers' objects shows up as slowness.
struct cs_arg { void *obj; long iters; };
static void *scratch_thread(void *p) {
    struct cs_arg *a = p;
    free(a->obj);
    char *mine = malloc(8);
    for (long i = 0; i < a->iters; i++) {
        for (int k = 0; k < 8; k++) mine[k]++;
        __asm__ volatile("" ::: "memory");
    }
    free(mine);
    return NULL;
}

static double cache_scratch(long iters) {
    pthread_t th[NTHREADS];
    struct cs_arg args[NTHREADS];
    for (int i = 0; i < NTHREADS; i++) args[i].obj = malloc(8), args[i].iters = iters;
    double t0 = now();
    for (int i = 0; i < NTHREADS; i++) pthread_create(&th[i], NULL, scratch_thread, &args[i]);
    for (int i = 0; i < NTHREADS; i++) pthread_join(th[i], NULL);
    return now() - t0;
}

// cache-thrash: workers repeatedly allocate a small object, write it
// many times and free it.
static void *thrash_thread(void *p) {
    long iters = (long)p;
    for (long r = 0; r < iters / 1000; r++) {
        char *mine = malloc(8);
        for (int i = 0; i < 1000; i++) {
            for (int k = 0; k < 8; k++) mine[k]++;
            __asm__ volatile("" ::: "memory");
        }
        free(mine);
    }
    return NULL;
}

static double cache_thrash(long iters) {
    pthread_t th[NTHREADS];
    double t0 = now();
    for (int i = 0; i < NTHREADS; i++) pthread_create(&th[i], NULL, thrash_thread, (void *)iters);
    for (int i = 0; i < NTHREADS; i++) pthread_join(th[i], NULL);
    return now() - t0;
}

// mstress: threads keep sets of long-tailed sizes, replace at random
// and occasionally hand a block to another thread's set.
struct ms_arg { int id; long ops; double secs; };
static void *ms_transfer[NTHREADS];
static pthread_mutex_t ms_mu = PTHREAD_MUTEX_INITIALIZER;
static void *mstress_thread(void *p) {
    struct ms_arg *a = p;
    enum { SLOTS = 2048 };
    void **set = calloc(SLOTS, sizeof *set);
    uint64_t s = 500 + a->id;
    double t0 = now();
    for (long i = 0; i < a->ops; i++) {
        size_t k = rnd(&s) % SLOTS;
        if (set[k]) free(set[k]);
        size_t n = tail_size(&s, 16 << 10);
        set[k] = malloc(n);
        ((char *)set[k])[0] = 1;
        if ((i & 63) == 0) {
            // Swap a block with the shared transfer slot of another thread.
            int other = (int)(rnd(&s) % NTHREADS);
            pthread_mutex_lock(&ms_mu);
            void *t = ms_transfer[other];
            ms_transfer[other] = set[k];
            pthread_mutex_unlock(&ms_mu);
            set[k] = t;
        }
    }
    a->secs = now() - t0;
    for (size_t k = 0; k < SLOTS; k++) free(set[k]);
    free(set);
    return NULL;
}

static double mstress(long ops) {
    pthread_t th[NTHREADS];
    struct ms_arg args[NTHREADS];
    for (int i = 0; i < NTHREADS; i++) {
        args[i].id = i;
        args[i].ops = ops;
        pthread_create(&th[i], NULL, mstress_thread, &args[i]);
    }
    double total = 0;
    for (int i = 0; i < NTHREADS; i++) {
        pthread_join(th[i], NULL);
        total += args[i].secs;
    }
    for (int i = 0; i < NTHREADS; i++) free(ms_transfer[i]), ms_transfer[i] = NULL;
    return total / NTHREADS;
}

// Short-lived threads that each allocate a little: heap setup and
// teardown.
static void *short_thread(void *p) {
    (void)p;
    void *b[64];
    for (int i = 0; i < 64; i++) b[i] = malloc(16 + i * 8);
    for (int i = 0; i < 64; i++) free(b[i]);
    return NULL;
}

static double thread_churn(long threads) {
    double t0 = now();
    for (long i = 0; i < threads; i += 4) {
        pthread_t th[4];
        for (int k = 0; k < 4; k++) pthread_create(&th[k], NULL, short_thread, NULL);
        for (int k = 0; k < 4; k++) pthread_join(th[k], NULL);
    }
    return now() - t0;
}

// ---------------------------------------------------------------------

int main(int argc, char **argv) {
    filter = argc > 1 ? argv[1] : NULL;
    uint64_t s = 0x9e3779b97f4a7c15ull;
    double t;

#define TIMED(name, ops, expr) do { if (selected(name)) { BEST(t, t_ = (expr)); report_ns(name, t, (double)(ops)); } } while (0)

    TIMED("malloc+free 16", 5000000, pair(16, 5000000));
    TIMED("malloc+free 128", 5000000, pair(128, 5000000));
    TIMED("malloc+free 4K", 2000000, pair(4096, 2000000));
    TIMED("malloc+free 64K", 500000, pair(65536, 500000));
    TIMED("malloc+free 1M", 200000, pair(1 << 20, 200000));
    TIMED("live set 16-256B", 3000000, live_set(4096, 16, 256, 3000000, &s));
    TIMED("live set 256B-8K", 1000000, live_set(2048, 256, 8192, 1000000, &s));
    TIMED("live set 64K-1M", 20000, live_set(64, 65536, 1 << 20, 20000, &s));
    TIMED("cfrac (LIFO bursts)", 3000000, cfrac(3000000, &s));
    TIMED("alloc-test 100k live", 2000000, alloc_test(100000, 2000000, &s));
    TIMED("sh6bench", 2000 * 4 * 3 * 14, sh6bench(&s));
    TIMED("glibc-simple", 2000 * 1000, glibc_simple(2000, &s));
    TIMED("malloc-large 1-16M", 400, malloc_large(400, &s));
    TIMED("calloc 64B", 2000000, calloc_small(2000000));
    TIMED("calloc 64K", 20000, calloc_medium(20000));
    TIMED("memalign 64/100B", 2000000, memalign_small(2000000));
    TIMED("aligned_alloc 4K/8K", 100000, memalign_page(100000));
    TIMED("realloc growth 16->1M", 200 * 17, realloc_growth(200));
    TIMED("realloc vectors x1.5", 1000000, realloc_vectors(1000000, &s));
    TIMED("tree build/teardown", 5 * 200000 * 2, tree(0));
    TIMED("tree teardown reversed", 5 * 200000 * 2, tree(1));
    TIMED("larson 4 threads", 1000000, larson(1000000));
    TIMED("producer/consumer", 400000, producer_consumer(400000, 0));
    TIMED("producer/consumer (sync only)", 400000, producer_consumer(400000, 1));
    TIMED("xmalloc-test 4 threads", 800 * 256 * 2, xmalloc_test(800));
    TIMED("cache-scratch", 20000000, cache_scratch(20000000));
    TIMED("cache-thrash", 20000000, cache_thrash(20000000));
    TIMED("mstress 4 threads", 500000, mstress(500000));
    TIMED("thread churn", 2000, thread_churn(2000));

    // Fragmentation: 100 MiB of small blocks, free 90% at random, then
    // allocate 30 MiB of 2 KiB blocks; report resident memory.
    if (selected("fragmentation")) {
        report_kb("fragmentation RSS before fill", rss_kb());
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
        report_kb("fragmentation RSS after 90% free", rss_kb());
        enum { K = 15000 };
        void **big = malloc(K * sizeof *big);
        for (int i = 0; i < K; i++) {
            big[i] = malloc(2048);
            memset(big[i], 1, 2048);
        }
        report_kb("fragmentation RSS after refill", rss_kb());
        for (int i = 0; i < K; i++) free(big[i]);
        for (int i = 0; i < M; i++) free(blocks[i]);
        free(big);
        free(blocks);
        report_kb("fragmentation RSS after all freed", rss_kb());
    }
    if (getenv("BENCH_RSS")) {
        report_kb("final RSS", rss_kb());
        // Let the allocator's decay run: wait, then touch it a little.
        struct timespec ts = {2, 0};
        nanosleep(&ts, NULL);
        for (int i = 0; i < 100; i++) free(malloc(64 + i * 512));
        free(malloc(2 << 20));
        report_kb("final RSS after decay", rss_kb());
    }
    return 0;
}
