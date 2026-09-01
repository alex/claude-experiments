// The allocator through the C API.
#include <errno.h>
#include <malloc.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

static uint64_t rng = 0x9e3779b97f4a7c15ull;
static size_t rnd(size_t n) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
    return (size_t)(rng % n);
}

int main(void) {
    void *p = malloc(100);
    CHECK(p != NULL);
    CHECK(((uintptr_t)p & 15) == 0);
    CHECK(malloc_usable_size(p) >= 100);
    memset(p, 'x', 100);
    p = realloc(p, 100000);
    CHECK(p != NULL);
    CHECK(((char *)p)[99] == 'x');
    free(p);

    char *z = calloc(10, 10);
    CHECK(z != NULL);
    for (int i = 0; i < 100; i++) CHECK(z[i] == 0);
    free(z);
    volatile size_t huge = (size_t)-1;
    CHECK(calloc(huge, 2) == NULL);
    CHECK(errno == ENOMEM);
    errno = 0;
    CHECK(reallocarray(NULL, huge, 2) == NULL);
    CHECK(errno == ENOMEM);

    void *a = NULL;
    CHECK(posix_memalign(&a, 4096, 10) == 0);
    CHECK(((uintptr_t)a & 4095) == 0);
    free(a);
    CHECK(posix_memalign(&a, 3, 10) == EINVAL);
    a = aligned_alloc(64, 128);
    CHECK(((uintptr_t)a & 63) == 0);
    free(a);
    a = memalign(1 << 20, 1 << 20);
    CHECK(((uintptr_t)a & ((1 << 20) - 1)) == 0);
    memset(a, 1, 1 << 20);
    free(a);
    free(NULL);

    // A random workload with a shadow copy of every block.
    enum { N = 2000 };
    static char *blocks[N];
    static size_t sizes[N];
    for (int round = 0; round < 40000; round++) {
        int i = (int)rnd(N);
        if (blocks[i]) {
            for (size_t k = 0; k < sizes[i]; k++) CHECK(blocks[i][k] == (char)(i * 7));
            if (rnd(4) == 0) {
                size_t ns = rnd(3000);
                char *q = realloc(blocks[i], ns);
                CHECK(q != NULL);
                for (size_t k = 0; k < (ns < sizes[i] ? ns : sizes[i]); k++) CHECK(q[k] == (char)(i * 7));
                memset(q, i * 7, ns);
                blocks[i] = q;
                sizes[i] = ns;
            } else {
                free(blocks[i]);
                blocks[i] = NULL;
            }
        } else {
            size_t s = rnd(10) == 0 ? rnd(300000) : rnd(500);
            blocks[i] = malloc(s);
            CHECK(blocks[i] != NULL);
            memset(blocks[i], i * 7, s);
            sizes[i] = s;
        }
    }
    for (int i = 0; i < N; i++) free(blocks[i]);

    char *d = strdup("dup me");
    CHECK(strcmp(d, "dup me") == 0);
    free(d);
    return 0;
}
