// Micro-benchmarks for the hot paths.  Built twice by `cargo xtask bench`
// (against rustlibc and against the host glibc, both static, both with
// -fno-builtin so the calls are real) and the results are printed side
// by side.  Each line of output is "name<TAB>value<TAB>unit".
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

// Runs `body` until at least 0.15 s have elapsed and returns the seconds
// per iteration.
#define MEASURE(result, body)                                    \
    do {                                                         \
        long iters = 1;                                          \
        double t0, t1;                                           \
        for (;;) {                                               \
            t0 = now();                                          \
            for (long i_ = 0; i_ < iters; i_++) { body; }        \
            t1 = now();                                          \
            if (t1 - t0 >= 0.15) break;                          \
            iters *= 2;                                          \
        }                                                        \
        result = (t1 - t0) / (double)iters;                      \
    } while (0)

static volatile unsigned long sink;
// glibc declares the read-only string functions `pure`, which would let the
// compiler hoist a call with loop-invariant arguments out of the timing
// loop; offsetting the pointer by 0 or 64 each iteration prevents that
// without changing alignment.
#define OFF(p) ((p) + ((i_ & 1) << 6))
static void report_bytes(const char *name, size_t n, double secs) {
    printf("%s\t%.2f\tGB/s\n", name, (double)n / secs / 1e9);
}
static void report_ns(const char *name, double secs) {
    printf("%s\t%.1f\tns/op\n", name, secs * 1e9);
}

static unsigned char *src, *dst;
static char *str;

static void bench_mem(void) {
    static const size_t sizes[] = {16, 64, 256, 4096, 65536, 1 << 20};
    char name[64];
    for (size_t k = 0; k < sizeof sizes / sizeof *sizes; k++) {
        size_t n = sizes[k];
        double s;
        snprintf(name, sizeof name, "memcpy %zu", n);
        MEASURE(s, memcpy(dst, src, n); sink += dst[n - 1]);
        report_bytes(name, n, s);
        snprintf(name, sizeof name, "memmove %zu (overlap)", n);
        MEASURE(s, memmove(dst + 8, dst, n); sink += dst[n - 1]);
        report_bytes(name, n, s);
        snprintf(name, sizeof name, "memset %zu", n);
        MEASURE(s, memset(dst, (int)i_, n); sink += dst[n - 1]);
        report_bytes(name, n, s);
        snprintf(name, sizeof name, "memcmp %zu (equal)", n);
        memcpy(dst, src, n);
        MEASURE(s, sink += (unsigned long)memcmp(OFF(dst), OFF(src), n));
        report_bytes(name, n, s);
        snprintf(name, sizeof name, "memchr %zu (miss)", n);
        MEASURE(s, sink += (unsigned long)memchr(OFF(src), 0, n));
        report_bytes(name, n, s);
        snprintf(name, sizeof name, "strlen %zu", n);
        str[n - 1] = 0;
        MEASURE(s, sink += strlen(str));
        report_bytes(name, n, s);
        str[n - 1] = 'a';
        snprintf(name, sizeof name, "strchr %zu (miss)", n);
        str[n] = 0;
        str[n + 64] = 0;
        MEASURE(s, sink += (unsigned long)strchr(OFF(str), 'z'));
        report_bytes(name, n, s);
        snprintf(name, sizeof name, "strcmp %zu (equal)", n);
        memcpy(dst, str, n + 128); // same bytes; dst has no NUL, so they differ at n
        MEASURE(s, sink += (unsigned long)strcmp(OFF(str), (char *)OFF(dst)));
        report_bytes(name, n, s);
        str[n] = 'a';
        str[n + 64] = 'a';
    }
    // memmem/strstr with a needle that appears only at the end.
    size_t n = 65536;
    str[n] = 0;
    memcpy(str + n - 8, "needle!", 8);
    double s;
    MEASURE(s, sink += (unsigned long)strstr(OFF(str), "needle!"));
    report_bytes("strstr 64K", n, s);
    MEASURE(s, sink += (unsigned long)memmem(OFF(str), n - 64, "needle!", 7));
    report_bytes("memmem 64K", n, s);
    memset(str + n - 8, 'a', 8);
    str[n] = 'a';
}

static void *churn(void *arg) {
    size_t rounds = (size_t)arg;
    void *ptrs[256];
    for (size_t r = 0; r < rounds; r++) {
        for (int i = 0; i < 256; i++) ptrs[i] = malloc((size_t)(16 + (i * 37) % 1000));
        for (int i = 0; i < 256; i++) free(ptrs[(i * 97) % 256]);
    }
    return NULL;
}

static void bench_malloc(void) {
    double s;
    MEASURE(s, free(malloc(64)));
    report_ns("malloc+free 64", s);
    MEASURE(s, free(malloc(4096)));
    report_ns("malloc+free 4096", s);
    MEASURE(s, free(malloc(1 << 20)));
    report_ns("malloc+free 1M", s);
    MEASURE(s, churn((void *)1));
    report_ns("malloc churn 256 mixed", s / 256);
    MEASURE(s, {
        pthread_t t[4];
        for (int i = 0; i < 4; i++) pthread_create(&t[i], NULL, churn, (void *)64);
        for (int i = 0; i < 4; i++) pthread_join(t[i], NULL);
    });
    report_ns("malloc churn 4 threads", s / (4 * 64 * 256));
    void *p = malloc(100);
    MEASURE(s, p = realloc(p, 100 + (i_ & 1) * 60));
    report_ns("realloc 100<->160", s);
    free(p);
}

static int cmp_int(const void *a, const void *b) {
    int x = *(const int *)a, y = *(const int *)b;
    return (x > y) - (x < y);
}

static void bench_stdlib(void) {
    double s;
    char buf[256];
    MEASURE(s, sink += (unsigned long)snprintf(buf, sizeof buf, "%d %s %x", (int)i_, "hello", 0xbeef));
    report_ns("snprintf %d %s %x", s);
    MEASURE(s, sink += (unsigned long)snprintf(buf, sizeof buf, "%f %g", 3.14159 * (double)i_, 2.5e-7));
    report_ns("snprintf %f %g", s);
    MEASURE(s, sink += (unsigned long)strtol("-123456789", NULL, 10));
    report_ns("strtol", s);
    MEASURE(s, sink += (unsigned long)strtod("3.14159265358979", NULL));
    report_ns("strtod", s);
    int a, b;
    MEASURE(s, sink += (unsigned long)sscanf("12345 67890", "%d %d", &a, &b));
    report_ns("sscanf %d %d", s);
    int *arr = malloc(100000 * sizeof(int));
    unsigned x = 1;
    MEASURE(s, {
        for (int i = 0; i < 100000; i++) { x = x * 1664525u + 1013904223u; arr[i] = (int)(x >> 8); }
        qsort(arr, 100000, sizeof(int), cmp_int);
    });
    report_ns("qsort 100k ints", s / 100000);
    free(arr);
    FILE *f = fopen("/dev/null", "w");
    MEASURE(s, fwrite("0123456789abcdef", 1, 16, f));
    report_ns("fwrite 16B buffered", s);
    MEASURE(s, fputc('x', f));
    report_ns("fputc", s);
    fclose(f);
    FILE *m = fmemopen(src, 65536, "r");
    MEASURE(s, { rewind(m); int c; while ((c = getc(m)) != EOF) sink += (unsigned long)c; });
    report_bytes("getc 64K", 65536, s);
    fclose(m);
    pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
    MEASURE(s, { pthread_mutex_lock(&mu); pthread_mutex_unlock(&mu); });
    report_ns("mutex lock+unlock", s);
    MEASURE(s, {
        pthread_t t;
        pthread_create(&t, NULL, churn, (void *)0);
        pthread_join(t, NULL);
    });
    report_ns("pthread_create+join", s);
}

int main(int argc, char **argv) {
    const char *only = argc > 1 ? argv[1] : "";
    size_t cap = (1 << 20) + 256;
    src = malloc(cap);
    dst = malloc(cap);
    str = malloc(cap);
    for (size_t i = 0; i < cap; i++) src[i] = (unsigned char)(1 + i % 250);
    memset(str, 'a', cap);
    memset(dst, 'a', cap);
    if (!*only || strcmp(only, "mem") == 0) bench_mem();
    if (!*only || strcmp(only, "malloc") == 0) bench_malloc();
    if (!*only || strcmp(only, "stdlib") == 0) bench_stdlib();
    return 0;
}
