// Clock calls go through the vDSO: they must agree with the raw system
// call and, being cheap, run many times within a short interval.
#include <sched.h>
#include <stdio.h>
#include <string.h>
#include <sys/auxv.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

int main(void) {
    CHECK(getauxval(AT_SYSINFO_EHDR) != 0);
    struct timespec a, b, raw;
    CHECK(clock_gettime(CLOCK_REALTIME, &a) == 0);
    CHECK(syscall(SYS_clock_gettime, CLOCK_REALTIME, &raw) == 0);
    CHECK(raw.tv_sec - a.tv_sec <= 1 && raw.tv_sec >= a.tv_sec);
    CHECK(clock_gettime(CLOCK_MONOTONIC, &a) == 0);
    long calls = 0;
    do {
        CHECK(clock_gettime(CLOCK_MONOTONIC, &b) == 0);
        CHECK(b.tv_sec > a.tv_sec || (b.tv_sec == a.tv_sec && b.tv_nsec >= a.tv_nsec));
        calls++;
    } while (b.tv_sec == a.tv_sec && b.tv_nsec - a.tv_nsec < 20 * 1000 * 1000);
    // Twenty milliseconds of system calls would be far fewer than this.
    CHECK(calls > 20000);
    CHECK(clock_gettime(CLOCK_MONOTONIC_COARSE, &b) == 0);
    CHECK(clock_gettime(999, &b) == -1);
    CHECK(time(NULL) >= raw.tv_sec);
    CHECK(sched_getcpu() >= 0);
    return 0;
}
