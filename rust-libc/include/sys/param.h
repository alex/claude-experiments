#ifndef _SYS_PARAM_H
#define _SYS_PARAM_H
#include <limits.h>
#include <sys/types.h>
#include <endian.h>

#define MAXPATHLEN PATH_MAX
#define NBBY CHAR_BIT
#define NGROUPS NGROUPS_MAX
#define MAXSYMLINKS 20
#define MAXHOSTNAMELEN 64
#define MAXNAMLEN 255
#define NOFILE 256
#define CANBSIZ 255
#define NCARGS 131072
#define EXEC_PAGESIZE 4096
#define MIN(a, b) (((a) < (b)) ? (a) : (b))
#define MAX(a, b) (((a) > (b)) ? (a) : (b))
#define howmany(n, d) (((n) + ((d) - 1)) / (d))
#define roundup(n, d) (howmany(n, d) * (d))
#define powerof2(n) !(((n) - 1) & (n))

#endif
