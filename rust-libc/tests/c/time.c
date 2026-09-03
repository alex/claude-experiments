// <time.h>: clocks, sleeping and calendar conversions.
#include <stdio.h>
#include <string.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

int main(void) {
    struct timespec a, b;
    CHECK(clock_gettime(CLOCK_MONOTONIC, &a) == 0);
    struct timespec nap = {0, 2000000};
    CHECK(nanosleep(&nap, NULL) == 0);
    CHECK(clock_gettime(CLOCK_MONOTONIC, &b) == 0);
    CHECK(b.tv_sec > a.tv_sec || (b.tv_sec == a.tv_sec && b.tv_nsec - a.tv_nsec >= 2000000));
    CHECK(clock_getres(CLOCK_REALTIME, &a) == 0 && a.tv_sec == 0);
    struct timeval tv;
    CHECK(gettimeofday(&tv, NULL) == 0 && tv.tv_sec > 1600000000 && tv.tv_usec < 1000000);
    time_t now = time(NULL);
    CHECK(now >= tv.tv_sec && now - tv.tv_sec <= 1);
    time_t also;
    CHECK(time(&also) == also);
    CHECK(usleep(1000) == 0 && sleep(0) == 0);
    CHECK(clock() >= 0);

    time_t t = 1700000000;
    struct tm tm;
    CHECK(gmtime_r(&t, &tm) != NULL);
    CHECK(tm.tm_year == 123 && tm.tm_mon == 10 && tm.tm_mday == 14 && tm.tm_hour == 22 && tm.tm_min == 13 && tm.tm_sec == 20);
    CHECK(tm.tm_wday == 2 && tm.tm_yday == 317 && tm.tm_isdst == 0 && strcmp(tm.tm_zone, "UTC") == 0);
    CHECK(timegm(&tm) == t && mktime(&tm) == t);
    struct tm *p = localtime(&t);
    CHECK(p && p->tm_hour == 22);
    char buf[64];
    CHECK(strftime(buf, sizeof buf, "%Y-%m-%d %H:%M:%S %a %b %j", &tm) == 31);
    printf("%s\n", buf);
    CHECK(strftime(buf, 5, "%Y-%m-%d", &tm) == 0);
    printf("%s", asctime(&tm));
    printf("%s", ctime(&t));
    CHECK(ctime_r(&t, buf) == buf && strcmp(buf, "Tue Nov 14 22:13:20 2023\n") == 0);
    tm.tm_mday += 30;  // normalises into December
    CHECK(mktime(&tm) == t + 30 * 86400 && tm.tm_mon == 11 && tm.tm_mday == 14);
    CHECK(difftime(10, 4) == 6.0);
    tzset();
    CHECK(strcmp(tzname[0], "UTC") == 0 && timezone == 0);
    return 0;
}
