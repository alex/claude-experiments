// printf family output, compared byte for byte against printf.stdout.
// cflags: -Wno-format -Wno-format-truncation
#include <errno.h>
#include <limits.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <wchar.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int vwrap(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    int n = vprintf(fmt, ap);
    va_end(ap);
    return n;
}

int main(void) {
    printf("plain\n");
    printf("%d %i %u %ld %lld %zu %x %X %o %c %s %%\n", 1, -2, 3u, 4L, 5LL, (size_t)6, 255, 255, 8, 'q', "str");
    printf("[%5d] [%-5d] [%05d] [%+d] [% d] [%.3d] [%8.3d]\n", 42, 42, 42, 42, 42, 42, 42);
    printf("[%10s] [%-10s] [%.2s] [%s]\n", "right", "left", "truncate", (char *)NULL);
    printf("%f %.2f %e %E %g %G %a\n", 3.14159, 2.71828, 12345.678, 0.000123, 100000.0, 1e-7, 1.0);
    printf("%.0f %.0f %.0f %.10f %.20f\n", 0.5, 1.5, 2.5, 1.0 / 3.0, 0.1);
    // The sign of the NaN a division produces is architecture specific.
    printf("%f %f %f %F\n", 1.0 / 0.0, -1.0 / 0.0, -__builtin_nan(""), 1.0 / 0.0);
    printf("%Lf %Le %Lg %La\n", 1.5L, 1.5L, 1.5L, 1.5L);
    printf("%hhd %hd %hhu %hu %jd %td\n", 300, 70000, 300, 70000, (intmax_t)-9, (ptrdiff_t)-3);
    printf("%p %p\n", (void *)0x1234, (void *)0);
    printf("%lc %ls|\n", (wint_t)0x263a, L"wide");
    printf("%2$s %1$s %2$s\n", "b", "a");
    printf("%*d|%-*d|%.*f\n", 6, 7, 6, 7, 2, 3.14159);
    printf("%d %d %d\n", INT_MAX, INT_MIN, 0);
    printf("%lu %ld\n", ULONG_MAX, LONG_MIN);
    printf("%#x %#o %#X %#.0f %#g\n", 255, 8, 255, 2.0, 1.0);
    printf("%.3s|%5.1s|%-5.1s|\n", "abcdef", "xyz", "xyz");
    printf("%c%c%c\n", 'a', 'b', 'c');
    int n = printf("count me\n");
    printf("%d\n", n);
    printf("%s\n", "no format args");
    errno = ENOENT;
    printf("%m\n");

    char buf[32];
    n = snprintf(buf, sizeof buf, "%s:%d", "key", 42);
    printf("%d %s\n", n, buf);
    n = snprintf(buf, 4, "%s:%d", "key", 42);
    printf("%d %s\n", n, buf);
    n = snprintf(NULL, 0, "%d", 123456);
    printf("%d\n", n);
    sprintf(buf, "%05.1f", 3.14159);
    printf("%s\n", buf);
    char *dyn = NULL;
    n = asprintf(&dyn, "%s-%s-%d", "a", "b", 3);
    printf("%d %s\n", n, dyn);
    free(dyn);
    vwrap("via %s %d\n", "va_list", 7);
    fprintf(stdout, "fprintf %d\n", 1);
    fflush(stdout);
    dprintf(1, "dprintf %d\n", 2);
    fputs("fputs\n", stdout);
    puts("puts");
    putchar('x');
    putchar('\n');
    fwrite("fwrite\n", 1, 7, stdout);
    // %n is refused.
    int dummy = 0;
    n = printf("%n", &dummy);
    printf("%d %d\n", n, errno == EINVAL);
    // Many args exercise the stack (overflow area) part of the va_list.
    printf("%d %d %d %d %d %d %d %d %d %d %f %f %f %f %f %f %f %f %f %f\n", 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0);
    // A large output goes through the buffer more than once.
    for (int i = 0; i < 3000; i++) printf("%d", i % 10);
    printf("\n");
    fprintf(stderr, "to stderr\n");
    return 0;
}
