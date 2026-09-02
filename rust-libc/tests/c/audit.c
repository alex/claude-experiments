// Regression tests for the issues found by the security self-audit.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <float.h>
#include <fnmatch.h>
#include <getopt.h>
#include <limits.h>
#include <locale.h>
#include <pthread.h>
#include <search.h>
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>
#include <wchar.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

extern int __sprintf_chk(char *, int, size_t, const char *, ...);
extern int __snprintf_chk(char *, size_t, int, size_t, const char *, ...);
extern int __fprintf_chk(FILE *, int, const char *, ...);
extern int __printf_chk(int, const char *, ...);

static int test_printf(void) {
    char buf[64];
    CHECK(snprintf(buf, sizeof buf, "cost: $%d, %s", 5, "ok") == 12 && strcmp(buf, "cost: $5, ok") == 0);
    CHECK(snprintf(buf, sizeof buf, "%2$s %1$s", "a", "b") == 3 && strcmp(buf, "b a") == 0);
    const char *volatile wide = "%18446744073709551615d";  // hide from gcc's format checks
    CHECK(snprintf(buf, sizeof buf, wide, 5) == -1);
    CHECK(snprintf(NULL, 0, "%.1500e", 1.0) == 1506);
    CHECK(snprintf(NULL, 0, "%.3000f", 0.5) == 3002);
    char *big = malloc(2000);
    CHECK(big && snprintf(big, 2000, "%.1500e", 1.0) == 1506);
    CHECK(strncmp(big, "1.000", 5) == 0 && strcmp(big + 1500, "00e+00") == 0);
    free(big);
    // Fortified variants take their va_list after the extra arguments.
    CHECK(__sprintf_chk(buf, 1, sizeof buf, "v=%d,%s", 42, "ok") == 7 && strcmp(buf, "v=42,ok") == 0);
    CHECK(__snprintf_chk(buf, sizeof buf, 1, sizeof buf, "%d-%d", 1, 2) == 3 && strcmp(buf, "1-2") == 0);
    char *mem = NULL;
    size_t memlen = 0;
    FILE *f = open_memstream(&mem, &memlen);
    CHECK(f && __fprintf_chk(f, 1, "%s=%d", "k", 7) == 3);
    fclose(f);
    CHECK(memlen == 3 && strcmp(mem, "k=7") == 0);
    free(mem);
    CHECK(__printf_chk(1, "x%dy\n", 5) == 4);
    return 0;
}

static int test_strtod(void) {
    CHECK(strtod("0x1.fffffffffffffffp-1023", NULL) == DBL_MIN);
    CHECK(strtod("0x1.fffffffffffffffp-1026", NULL) == 0x1p-1025);
    char s[256];
    memset(s, 'a', 200);
    memcpy(s, "nan(", 4);
    s[200] = ')';
    s[201] = 0;
    char *end;
    CHECK(strtod(s, &end) != strtod(s, &end) && end == s + 201);
    return 0;
}

static int test_env(void) {
    // Entries shorter than the name must not be over-read.
    CHECK(setenv("A", "1", 1) == 0);
    CHECK(getenv("A_VERY_LONG_NAME_THAT_IS_LONGER_THAN_ANY_SIMD_VECTOR_XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX") == NULL);
    CHECK(strcmp(getenv("A"), "1") == 0);
    // Passing the entry itself back is not a free of it.
    char *entry = getenv("A") - 2;
    CHECK(putenv(entry) == 0 && strcmp(getenv("A"), "1") == 0);
    const char *volatile null = NULL;
    CHECK(strnlen(null, 0) == 0);
    return 0;
}

static sigjmp_buf jb;

static int test_sigsetjmp(void) {
    // siglongjmp must restore rbx to its value at sigsetjmp, not the
    // saved signal mask.
    long r;
    asm volatile(
        "push %%rbp\n\t"
        "mov %%rsp, %%rbp\n\t"
        "and $-16, %%rsp\n\t"
        "mov %1, %%r12\n\t"
        "mov $0x1234567, %%rbx\n\t"
        "mov %%r12, %%rdi\n\t"
        "mov $1, %%esi\n\t"
        "call sigsetjmp\n\t"
        "test %%eax, %%eax\n\t"
        "jnz 1f\n\t"
        "xor %%ebx, %%ebx\n\t"
        "mov %%r12, %%rdi\n\t"
        "mov $1, %%esi\n\t"
        "call siglongjmp\n\t"
        "1:\n\t"
        "mov %%rbx, %0\n\t"
        "mov %%rbp, %%rsp\n\t"
        "pop %%rbp\n\t"
        : "=r"(r)
        : "r"(jb)
        : "rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "rbx", "memory", "cc");
    CHECK(r == 0x1234567);
    return 0;
}

static int test_getopt(void) {
    char *argv[] = {"prog", "file", "-o", "out", "-x", "rest", NULL};
    optind = 1;
    CHECK(getopt(6, argv, "o:x") == 'o' && strcmp(optarg, "out") == 0);
    CHECK(getopt(6, argv, "o:x") == 'x');
    CHECK(getopt(6, argv, "o:x") == -1);
    CHECK(optind == 4 && strcmp(argv[4], "file") == 0 && strcmp(argv[5], "rest") == 0);
    char *argv2[] = {"prog", "in", "--name", "val", "-ab", "-c", "z", NULL};
    struct option longs[] = {{"name", required_argument, NULL, 'n'}, {0, 0, 0, 0}};
    optind = 1;
    CHECK(getopt_long(7, argv2, "abc:", longs, NULL) == 'n' && strcmp(optarg, "val") == 0);
    CHECK(getopt_long(7, argv2, "abc:", longs, NULL) == 'a');
    CHECK(getopt_long(7, argv2, "abc:", longs, NULL) == 'b');
    CHECK(getopt_long(7, argv2, "abc:", longs, NULL) == 'c' && strcmp(optarg, "z") == 0);
    CHECK(getopt_long(7, argv2, "abc:", longs, NULL) == -1);
    CHECK(optind == 6 && strcmp(argv2[6], "in") == 0);
    // A stale mid-cluster position from an abandoned parse is harmless.
    char *argv3[] = {"prog", "-ab", NULL};
    optind = 1;
    CHECK(getopt(2, argv3, "ab") == 'a');
    char *argv4[] = {"prog", "-x", NULL};
    optind = 1;
    CHECK(getopt(2, argv4, "abx") == 'x');
    return 0;
}

static int test_stdio(void) {
    char a[] = "/tmp/audit_a_XXXXXX", b[] = "/tmp/audit_b_XXXXXX";
    int fa = mkstemp(a), fb = mkstemp(b);
    CHECK(fa >= 0 && fb >= 0);
    close(fb);
    // freopen keeps the stream's descriptor number even when a lower one
    // is free.
    int hole = open("/dev/null", O_RDONLY);
    FILE *f = fdopen(fa, "w");
    CHECK(f && fileno(f) == fa);
    close(hole);
    CHECK(freopen(b, "w", f) == f && fileno(f) == fa);
    fputs("hi", f);
    fclose(f);
    f = fopen(b, "r");
    char buf[8] = {0};
    CHECK(f && fread(buf, 1, 8, f) == 2 && strcmp(buf, "hi") == 0);
    fclose(f);
    // fdopen honours "e".
    int fd = open(b, O_RDONLY);
    f = fdopen(fd, "re");
    CHECK(f && (fcntl(fd, F_GETFD) & FD_CLOEXEC));
    fclose(f);
    unlink(a);
    unlink(b);
    // A memory stream's seek gap reads as zeros.
    char *mem = NULL;
    size_t memlen = 0;
    f = open_memstream(&mem, &memlen);
    CHECK(f && fseek(f, 100, SEEK_SET) == 0 && fputc('x', f) == 'x' && fflush(f) == 0);
    CHECK(memlen == 101 && mem[100] == 'x');
    for (int i = 0; i < 100; i++) CHECK(mem[i] == 0);
    fclose(f);
    free(mem);
    // ftrylockfile on a stream locked by us succeeds recursively; the
    // lock is fully released after matching unlocks.
    flockfile(stdout);
    CHECK(ftrylockfile(stdout) == 0);
    funlockfile(stdout);
    funlockfile(stdout);
    return 0;
}

static int test_time(void) {
    struct tm tm = {0};
    tm.tm_year = 124;
    tm.tm_mon = 1;
    tm.tm_mday = 29;
    char buf[11];
    CHECK(strftime(buf, sizeof buf, "%Y-%m-%d", &tm) == 10 && strcmp(buf, "2024-02-29") == 0);
    CHECK(strftime(buf, 10, "%Y-%m-%d", &tm) == 0);
    time_t huge = LLONG_MAX;
    CHECK(ctime(&huge) == NULL);
    CHECK(localtime(&huge) == NULL && errno == EOVERFLOW);
    tm.tm_year = 98100;
    errno = 0;
    CHECK(asctime(&tm) == NULL && errno == EOVERFLOW);
    tm.tm_year = 124;
    tm.tm_wday = 9;
    CHECK(asctime(&tm) == NULL && errno == EINVAL);
    tm.tm_wday = 4;
    CHECK(strcmp(asctime(&tm), "Thu Feb 29 00:00:00 2024\n") == 0);
    return 0;
}

static void *rd_hold(void *arg) {
    pthread_rwlock_t *l = arg;
    pthread_rwlock_rdlock(l);
    struct timespec ts = {0, 200 * 1000 * 1000};
    nanosleep(&ts, NULL);
    pthread_rwlock_unlock(l);
    return NULL;
}

static pthread_barrier_t bar;
static int serial_count;
static void *bar_worker(void *arg) {
    (void)arg;
    for (int i = 0; i < 2000; i++) {
        if (pthread_barrier_wait(&bar) == PTHREAD_BARRIER_SERIAL_THREAD)
            __sync_fetch_and_add(&serial_count, 1);
    }
    return NULL;
}

static int test_threads(void) {
    // A writer that times out must not leave readers blocked.
    pthread_rwlock_t l = PTHREAD_RWLOCK_INITIALIZER;
    pthread_t t;
    CHECK(pthread_create(&t, NULL, rd_hold, &l) == 0);
    struct timespec ts = {0, 20 * 1000 * 1000};
    nanosleep(&ts, NULL);
    clock_gettime(CLOCK_REALTIME, &ts);
    ts.tv_nsec += 30 * 1000 * 1000;
    if (ts.tv_nsec >= 1000000000) { ts.tv_sec++; ts.tv_nsec -= 1000000000; }
    CHECK(pthread_rwlock_timedwrlock(&l, &ts) == ETIMEDOUT);
    CHECK(pthread_rwlock_tryrdlock(&l) == 0);
    pthread_rwlock_unlock(&l);
    pthread_join(t, NULL);
    // Barrier rounds stay in step under contention.
    CHECK(pthread_barrier_init(&bar, NULL, 3) == 0);
    pthread_t ws[3];
    for (int i = 0; i < 3; i++) CHECK(pthread_create(&ws[i], NULL, bar_worker, NULL) == 0);
    for (int i = 0; i < 3; i++) pthread_join(ws[i], NULL);
    CHECK(serial_count == 2000);
    // A deleted key's values are not visible through its reused slot.
    pthread_key_t k1, k2;
    CHECK(pthread_key_create(&k1, NULL) == 0);
    CHECK(pthread_setspecific(k1, (void *)1) == 0);
    CHECK(pthread_key_delete(k1) == 0);
    CHECK(pthread_key_create(&k2, NULL) == 0);
    CHECK(pthread_getspecific(k2) == NULL);
    pthread_key_delete(k2);
    return 0;
}

static int test_misc(void) {
    struct termios tio;
    memset(&tio, 0xff, sizeof tio);
    cfmakeraw(&tio);
    CHECK(!(tio.c_lflag & ECHONL) && !(tio.c_iflag & IGNCR) && (tio.c_iflag & IGNPAR));
    CHECK(access("/", R_OK) == 0);
    errno = 0;
    CHECK(hcreate((size_t)-1) == 0 && errno == ENOMEM);
    CHECK(fnmatch("[\\]", "\\", FNM_NOESCAPE) == 0);
    CHECK(fnmatch("[\\]]", "]", 0) == 0);
    // Long wide numeric strings are parsed in full.
    wchar_t w[320];
    w[0] = L'1';
    for (int i = 1; i <= 300; i++) w[i] = L'0';
    w[301] = L'x';
    w[302] = 0;
    wchar_t *end;
    CHECK(wcstod(w, &end) == 1e300 && end == w + 301);
    errno = 0;
    CHECK(wcstol(w, &end, 10) == LONG_MAX && errno == ERANGE && end == w + 301);
    // The save/restore idiom aliases setlocale's own buffer.
    char *saved = setlocale(LC_ALL, NULL);
    CHECK(saved && setlocale(LC_ALL, saved) != NULL);
    // A hex float with a huge precision pads with zeros before the exponent.
    char big[128];
    CHECK(snprintf(big, sizeof big, "%.100a", 1.0) == 107 && strcmp(big + 100, "0000p+0") == 0);
    return 0;
}

static void *hold_stdin_like(void *arg) {
    FILE *f = arg;
    fgetc(f);  // blocks forever holding the stream lock
    return NULL;
}

int main(void) {
    int r;
    if ((r = test_printf())) return r;
    if ((r = test_strtod())) return r;
    if ((r = test_env())) return r;
    if ((r = test_sigsetjmp())) return r;
    if ((r = test_getopt())) return r;
    if ((r = test_stdio())) return r;
    if ((r = test_time())) return r;
    if ((r = test_threads())) return r;
    if ((r = test_misc())) return r;
    // exit() must not wait for a stream another thread holds while
    // blocked in a read.
    int p[2];
    if (pipe(p) != 0) return 200;
    FILE *f = fdopen(p[0], "r");
    pthread_t t;
    if (pthread_create(&t, NULL, hold_stdin_like, f) != 0) return 201;
    struct timespec ts = {0, 50 * 1000 * 1000};
    nanosleep(&ts, NULL);
    printf("done\n");
    return 0;
}
