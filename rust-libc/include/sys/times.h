#ifndef _SYS_TIMES_H
#define _SYS_TIMES_H
#include <bits/features.h>
#include <time.h>

struct tms {
    clock_t tms_utime, tms_stime, tms_cutime, tms_cstime;
};

__BEGIN_DECLS
clock_t times(struct tms *);
__END_DECLS

#endif
