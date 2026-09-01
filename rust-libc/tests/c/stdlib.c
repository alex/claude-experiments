// <stdlib.h>: conversions, sorting, environment, rand.
#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

static int cmp_int(const void *a, const void *b) {
    int x = *(const int *)a, y = *(const int *)b;
    return (x > y) - (x < y);
}

static int cmp_str(const void *a, const void *b) {
    return strcmp(*(char *const *)a, *(char *const *)b);
}

int main(void) {
    char *end;
    CHECK(strtol("  -123abc", &end, 10) == -123 && strcmp(end, "abc") == 0);
    CHECK(strtol("0x1F", NULL, 0) == 31);
    CHECK(strtol("077", NULL, 0) == 63);
    CHECK(strtoul("-1", NULL, 10) == ULONG_MAX);
    errno = 0;
    CHECK(strtol("99999999999999999999", NULL, 10) == LONG_MAX && errno == ERANGE);
    errno = 0;
    CHECK(strtoll("-9223372036854775808", NULL, 10) == LLONG_MIN && errno == 0);
    CHECK(strtoull("18446744073709551615", NULL, 10) == ULLONG_MAX);
    CHECK(strtoimax("-5", NULL, 10) == -5 && strtoumax("5", NULL, 10) == 5);
    CHECK(atoi("42") == 42 && atol("-7") == -7 && atoll("123456789012") == 123456789012LL);
    CHECK(strtod("1.5e2xyz", &end) == 150.0 && strcmp(end, "xyz") == 0);
    CHECK(strtod("0x1.8p1", NULL) == 3.0);
    CHECK(strtod("-inf", NULL) < -1e308);
    CHECK(strtod("nan", NULL) != strtod("nan", NULL));
    CHECK(atof("2.5") == 2.5);
    CHECK(strtof("0.1", NULL) == 0.1f);
    errno = 0;
    CHECK(strtod("1e999", NULL) > 1e308 && errno == ERANGE);
    CHECK(strtod("junk", &end) == 0.0 && end != NULL && *end == 'j');

    int v[] = {5, 3, 9, 1, 7, 3, 8, 2};
    qsort(v, 8, sizeof v[0], cmp_int);
    for (int i = 1; i < 8; i++) CHECK(v[i - 1] <= v[i]);
    int key = 7;
    int *found = bsearch(&key, v, 8, sizeof v[0], cmp_int);
    CHECK(found && *found == 7);
    key = 4;
    CHECK(bsearch(&key, v, 8, sizeof v[0], cmp_int) == NULL);
    const char *words[] = {"pear", "apple", "fig"};
    qsort(words, 3, sizeof words[0], cmp_str);
    CHECK(strcmp(words[0], "apple") == 0 && strcmp(words[2], "pear") == 0);

    CHECK(getenv("TESTVAR") && strcmp(getenv("TESTVAR"), "value") == 0);
    CHECK(getenv("NOPE") == NULL);
    CHECK(setenv("NEWVAR", "hello", 1) == 0);
    CHECK(strcmp(getenv("NEWVAR"), "hello") == 0);
    CHECK(setenv("NEWVAR", "other", 0) == 0);
    CHECK(strcmp(getenv("NEWVAR"), "hello") == 0);
    CHECK(unsetenv("NEWVAR") == 0 && getenv("NEWVAR") == NULL);
    CHECK(strcmp(getenv("TESTVAR"), "value") == 0);
    static char put[] = "PUTVAR=1";
    CHECK(putenv(put) == 0 && strcmp(getenv("PUTVAR"), "1") == 0);
    CHECK(setenv("=bad", "x", 1) == -1 && errno == EINVAL);
    // environ still walks all entries.
    int n = 0;
    for (char **e = environ; *e; e++) n++;
    CHECK(n >= 2);

    srand(1);
    int r1 = rand(), r2 = rand();
    srand(1);
    CHECK(rand() == r1 && rand() == r2);
    CHECK(r1 >= 0 && r1 <= RAND_MAX);
    unsigned seed = 5;
    CHECK(rand_r(&seed) != rand_r(&seed));

    CHECK(abs(-3) == 3 && labs(-3L) == 3 && llabs(-3LL) == 3);
    div_t dv = div(7, 2);
    CHECK(dv.quot == 3 && dv.rem == 1);
    ldiv_t ldv = ldiv(-7, 2);
    CHECK(ldv.quot == -3 && ldv.rem == -1);
    lldiv_t lldv = lldiv(7, -2);
    CHECK(lldv.quot == -3 && lldv.rem == 1);
    imaxdiv_t idv = imaxdiv(9, 4);
    CHECK(idv.quot == 2 && idv.rem == 1 && imaxabs(-9) == 9);
    return 0;
}
