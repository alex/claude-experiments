// Constructors, atexit ordering, environ, TLS variables and the stack
// protector all depend on startup having done its job.
// expect-exit: 7
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/auxv.h>

static int order[8];
static int n;

__attribute__((constructor)) static void ctor(void) { order[n++] = 1; }
static void at1(void) { order[n++] = 3; }
static void at2(void) { order[n++] = 2; }
static void at3(void) {
    order[n++] = 4;
    // Everything ran in the expected order: 1 (ctor), 2 (at2), 3 (at1), 4.
    if (n == 4 && order[0] == 1 && order[1] == 2 && order[2] == 3 && order[3] == 4)
        _exit(7);
    _exit(1);
}
__attribute__((destructor)) static void dtor(void) {
    // Destructors run after atexit handlers.
    at3();
}

static __thread int tls_var = 42;
static __thread char tls_buf[100];

int main(void) {
    if (order[0] != 1) return 10;
    if (!environ || !environ[0]) return 11;
    if (!getauxval(AT_PAGESZ)) return 12;
    if (tls_var != 42) return 13;
    tls_var = 5;
    if (tls_var != 5) return 14;
    // Force a stack protector canary read.
    char buf[64];
    memset(buf, 'a', sizeof buf - 1);
    buf[63] = 0;
    if (strlen(buf) != 63) return 15;
    for (int i = 0; i < 100; i++) tls_buf[i] = (char)i;
    if (tls_buf[99] != 99) return 16;
    atexit(at1);
    atexit(at2);
    exit(0);
}
