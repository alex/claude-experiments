// Static PIE support: relocated data, constructors, the load bias
// reported to the unwinder, and RELRO protection. Built both as a
// fixed-address executable and (cargo xtask --pie test) as a static PIE.
#include <link.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

static int ctor_ran;
__attribute__((constructor)) static void ctor(void) { ctor_ran = 1; }

static int one(void) { return 1; }
static int two(void) { return 2; }
// Pointers in const data need relative relocations in a PIE and land in
// the RELRO segment.
static int (*const table[])(void) = { one, two };
static const char *const names[] = { "alpha", "beta" };

static int cb(struct dl_phdr_info *info, size_t size, void *data) {
    (void)size;
    *(unsigned long *)data = info->dlpi_addr;
    return 1;
}

// Permissions of the mapping containing `addr`, from /proc/self/maps.
static int perms(const void *addr, char out[5]) {
    FILE *f = fopen("/proc/self/maps", "r");
    if (!f) return 0;
    char line[256];
    int found = 0;
    while (fgets(line, sizeof line, f)) {
        unsigned long lo, hi;
        char p[8];
        if (sscanf(line, "%lx-%lx %4s", &lo, &hi, p) == 3 && (unsigned long)addr >= lo && (unsigned long)addr < hi) {
            memcpy(out, p, 5);
            found = 1;
            break;
        }
    }
    fclose(f);
    return found;
}

int main(void) {
    CHECK(ctor_ran == 1);
    CHECK(table[0]() == 1 && table[1]() == 2);
    CHECK(strcmp(names[1], "beta") == 0);
    unsigned long bias = 1;
    CHECK(dl_iterate_phdr(cb, &bias) == 1);
#ifdef __PIE__
    CHECK(bias != 0);
    CHECK((unsigned long)main > bias);
#else
    CHECK(bias == 0);
#endif
    // The pointer tables were relocated and then made read-only.
    char p[5];
    CHECK(perms(table, p));
    CHECK(p[0] == 'r' && p[1] == '-');
    // Ordinary data is still writable, of course.
    CHECK(perms(&ctor_ran, p));
    CHECK(p[1] == 'w');
    printf("bias %s\n", bias ? "nonzero" : "zero");
    return 0;
}
