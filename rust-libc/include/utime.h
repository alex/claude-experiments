#ifndef _UTIME_H
#define _UTIME_H
#include <bits/features.h>

#define __NEED_time_t
#include <bits/alltypes.h>

struct utimbuf {
    time_t actime;
    time_t modtime;
};

__BEGIN_DECLS
int utime(const char *, const struct utimbuf *);
__END_DECLS

#endif
