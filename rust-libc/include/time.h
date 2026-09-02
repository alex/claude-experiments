#ifndef _TIME_H
#define _TIME_H
#include <bits/features.h>

#define __NEED_size_t
#define __NEED_time_t
#define __NEED_clockid_t
#define __NEED_struct_timespec
#include <bits/alltypes.h>

#ifdef __cplusplus
#define NULL 0L
#else
#define NULL ((void *)0)
#endif

typedef long clock_t;
typedef void *timer_t;

struct tm {
    int tm_sec;
    int tm_min;
    int tm_hour;
    int tm_mday;
    int tm_mon;
    int tm_year;
    int tm_wday;
    int tm_yday;
    int tm_isdst;
    long tm_gmtoff;
    const char *tm_zone;
};

struct itimerspec {
    struct timespec it_interval;
    struct timespec it_value;
};

#define CLOCKS_PER_SEC 1000000L
#define CLOCK_REALTIME 0
#define CLOCK_MONOTONIC 1
#define CLOCK_PROCESS_CPUTIME_ID 2
#define CLOCK_THREAD_CPUTIME_ID 3
#define CLOCK_MONOTONIC_RAW 4
#define CLOCK_REALTIME_COARSE 5
#define CLOCK_MONOTONIC_COARSE 6
#define CLOCK_BOOTTIME 7
#define TIMER_ABSTIME 1

#define TIME_UTC 1

__BEGIN_DECLS

int clock_gettime(clockid_t, struct timespec *);
int timespec_get(struct timespec *, int);
int clock_getres(clockid_t, struct timespec *);
int clock_settime(clockid_t, const struct timespec *);
int clock_nanosleep(clockid_t, int, const struct timespec *, struct timespec *);
int nanosleep(const struct timespec *, struct timespec *);
time_t time(time_t *);
clock_t clock(void);
double difftime(time_t, time_t);
time_t mktime(struct tm *);
time_t timegm(struct tm *);
struct tm *gmtime(const time_t *);
struct tm *gmtime_r(const time_t *__RESTRICT, struct tm *__RESTRICT);
struct tm *localtime(const time_t *);
struct tm *localtime_r(const time_t *__RESTRICT, struct tm *__RESTRICT);
char *asctime(const struct tm *);
char *asctime_r(const struct tm *__RESTRICT, char *__RESTRICT);
char *ctime(const time_t *);
char *ctime_r(const time_t *, char *);
size_t strftime(char *__RESTRICT, size_t, const char *__RESTRICT, const struct tm *__RESTRICT);
void tzset(void);

extern char *tzname[2];
extern long timezone;
extern int daylight;

__END_DECLS

#endif
