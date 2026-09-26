#ifndef _SYS_SYSINFO_H
#define _SYS_SYSINFO_H
#include <bits/features.h>

struct sysinfo {
    long uptime;
    unsigned long loads[3];
    unsigned long totalram, freeram, sharedram, bufferram;
    unsigned long totalswap, freeswap;
    unsigned short procs, pad;
    unsigned long totalhigh, freehigh;
    unsigned mem_unit;
    char __reserved[20 - 2 * sizeof(long) - sizeof(unsigned)];
};

__BEGIN_DECLS
int sysinfo(struct sysinfo *);
__END_DECLS

#endif
