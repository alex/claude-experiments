// C11 <threads.h> and the C++ runtime hooks (__cxa_atexit, dl_iterate_phdr).
#include <link.h>
#include <stdlib.h>
#include <string.h>
#include <threads.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); _exit(__LINE__); } } while (0)

static mtx_t mtx;
static cnd_t cnd;
static once_flag once = ONCE_FLAG_INIT;
static tss_t key;
static int counter, ready, once_runs, dtor_runs;
static thread_local int tl = 3;

static void init(void) { once_runs++; }
static void dtor(void *p) { (void)p; dtor_runs++; }

static int worker(void *arg) {
    call_once(&once, init);
    tl += (int)(long)arg;
    CHECK(tss_set(key, &tl) == thrd_success && tss_get(key) == &tl);
    for (int i = 0; i < 1000; i++) {
        mtx_lock(&mtx);
        counter++;
        mtx_unlock(&mtx);
    }
    mtx_lock(&mtx);
    ready++;
    cnd_signal(&cnd);
    mtx_unlock(&mtx);
    return (int)(long)arg * 2;
}

extern int __cxa_atexit(void (*)(void *), void *, void *);
extern void *__dso_handle;
static int cxa_arg;
static void cxa_handler(void *p) {
    if (p == &cxa_arg && cxa_arg == 5) _exit(0);
    _exit(77);
}

static int seen_phdr;
static int phdr_cb(struct dl_phdr_info *info, size_t size, void *data) {
    CHECK(size >= sizeof *info && data == &seen_phdr && info->dlpi_phnum > 0);
    for (int i = 0; i < info->dlpi_phnum; i++)
        if (info->dlpi_phdr[i].p_type == PT_LOAD) seen_phdr++;
    return 0;
}

int main(void) {
    CHECK(mtx_init(&mtx, mtx_plain) == thrd_success && cnd_init(&cnd) == thrd_success);
    CHECK(tss_create(&key, dtor) == thrd_success);
    thrd_t t[4];
    for (long i = 0; i < 4; i++) CHECK(thrd_create(&t[i], worker, (void *)(i + 1)) == thrd_success);
    mtx_lock(&mtx);
    while (ready < 4) cnd_wait(&cnd, &mtx);
    mtx_unlock(&mtx);
    for (long i = 0; i < 4; i++) {
        int res = -1;
        CHECK(thrd_join(t[i], &res) == thrd_success && res == (i + 1) * 2);
    }
    CHECK(counter == 4000 && once_runs == 1 && dtor_runs == 4 && tl == 3);
    CHECK(thrd_equal(thrd_current(), thrd_current()) && mtx_trylock(&mtx) == thrd_success && mtx_trylock(&mtx) == thrd_busy);
    mtx_unlock(&mtx);
    struct timespec ts = {0, 1000000};
    CHECK(thrd_sleep(&ts, NULL) == 0);
    mtx_t rm;
    CHECK(mtx_init(&rm, mtx_plain | mtx_recursive) == thrd_success && mtx_lock(&rm) == thrd_success && mtx_lock(&rm) == thrd_success);
    mtx_unlock(&rm);
    mtx_unlock(&rm);
    mtx_destroy(&rm);
    CHECK(dl_iterate_phdr(phdr_cb, &seen_phdr) == 0 && seen_phdr > 0);
    cxa_arg = 5;
    CHECK(__cxa_atexit(cxa_handler, &cxa_arg, &__dso_handle) == 0);
    exit(3);  // cxa_handler turns this into exit status 0
}
