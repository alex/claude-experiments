// A double free must be detected and abort the process.
// expect-signal: SIGABRT
#include <stdlib.h>

int main(void) {
    char *volatile p = malloc(32);
    free(p);
    free(p);
    return 0;
}
