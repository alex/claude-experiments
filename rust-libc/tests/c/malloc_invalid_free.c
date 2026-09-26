// Freeing an interior pointer must be detected and abort the process.
// expect-signal: SIGABRT
#include <stdlib.h>

static void *offset(void *p, long n) {
    volatile long off = n;  // hide the offset from gcc's diagnostics
    return (char *)p + off;
}

int main(void) {
    char *p = malloc(64);
    free(offset(p, 16));
    return 0;
}
