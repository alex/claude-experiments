// Time zones: POSIX TZ rules, zoneinfo files, localtime/mktime round
// trips, tzname/timezone and strftime %Z.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

int main(void) {
    setenv("TZ", "EST5EDT,M3.2.0,M11.1.0", 1);
    tzset();
    CHECK(strcmp(tzname[0], "EST") == 0 && strcmp(tzname[1], "EDT") == 0);
    CHECK(timezone == 18000 && daylight == 1);
    time_t t = 1710054000; // 2024-03-10 07:00:00Z: first second of EDT
    struct tm tm;
    CHECK(localtime_r(&t, &tm) != NULL);
    CHECK(tm.tm_hour == 3 && tm.tm_min == 0 && tm.tm_isdst == 1 && tm.tm_gmtoff == -14400);
    CHECK(strcmp(tm.tm_zone, "EDT") == 0);
    char buf[64];
    strftime(buf, sizeof buf, "%Y-%m-%d %H:%M:%S %Z %z", &tm);
    puts(buf);
    time_t back = mktime(&tm);
    CHECK(back == t);
    t -= 1;
    CHECK(localtime_r(&t, &tm) && tm.tm_hour == 1 && tm.tm_isdst == 0);
    strftime(buf, sizeof buf, "%H:%M:%S %Z", &tm);
    puts(buf);
    // mktime normalises and picks the zone: 2024-07-04 12:00 local is EDT.
    memset(&tm, 0, sizeof tm);
    tm.tm_year = 124; tm.tm_mon = 6; tm.tm_mday = 4; tm.tm_hour = 12; tm.tm_isdst = -1;
    t = mktime(&tm);
    CHECK(t == 1720108800 && tm.tm_isdst == 1);
    // An explicit standard-time request for the same wall clock is an hour later.
    tm.tm_hour = 12; tm.tm_isdst = 0;
    CHECK(mktime(&tm) == 1720108800 + 3600);
    puts(ctime(&t));

    setenv("TZ", "UTC0", 1);
    tzset();
    CHECK(strcmp(tzname[0], "UTC") == 0 && timezone == 0 && daylight == 0);
    t = 0;
    CHECK(localtime_r(&t, &tm) && tm.tm_hour == 0 && tm.tm_gmtoff == 0);

    if (access("/usr/share/zoneinfo/Europe/Berlin", R_OK) == 0) {
        setenv("TZ", "Europe/Berlin", 1);
        tzset();
        t = 1720108800; // 2024-07-04 16:00:00Z = 18:00 CEST
        CHECK(localtime_r(&t, &tm) && tm.tm_hour == 18 && tm.tm_isdst == 1 && strcmp(tm.tm_zone, "CEST") == 0);
        CHECK(mktime(&tm) == t);
        t = 1704067200; // 2024-01-01 00:00Z = 01:00 CET
        CHECK(localtime_r(&t, &tm) && tm.tm_hour == 1 && tm.tm_isdst == 0 && tm.tm_gmtoff == 3600);
        // Far future uses the file's footer rule.
        t = 4102444800 + 200 * 86400;
        CHECK(localtime_r(&t, &tm) && tm.tm_isdst == 1);
        setenv("TZ", ":/usr/share/zoneinfo/Europe/Berlin", 1);
        tzset();
        CHECK(strcmp(tzname[0], "CET") == 0 && strcmp(tzname[1], "CEST") == 0);
        // Names that escape the zoneinfo directory are ignored (UTC).
        setenv("TZ", "../../../etc/passwd", 1);
        tzset();
        CHECK(strcmp(tzname[0], "UTC") == 0);
    }
    unsetenv("TZ");
    tzset();
    CHECK(tzname[0] != NULL);
    return 0;
}
