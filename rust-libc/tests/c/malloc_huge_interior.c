// A pointer into the middle of a block larger than a 16 MiB segment lands
// on a segment boundary whose "header" is user data; free() must still
// reject it (via the mapping registry) rather than trust that header.
// expect-signal: SIGABRT
#include <stdlib.h>
#include <string.h>

int main(void) {
    size_t size = 40u << 20;
    char *p = malloc(size);
    if (!p) return 1;
    memset(p, 0x5a, size);
    volatile size_t off = 16u << 20;
    off -= (size_t)p & ((16u << 20) - 1);  // first 16 MiB boundary inside the block
    free(p + off);
    return 0;
}
