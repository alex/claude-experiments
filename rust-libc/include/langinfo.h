#ifndef _LANGINFO_H
#define _LANGINFO_H
#include <bits/features.h>

typedef int nl_item;
#define CODESET 14
#define D_T_FMT 0x2002c
#define D_FMT 0x2002d
#define T_FMT 0x2002e
#define T_FMT_AMPM 0x2002f
#define AM_STR 0x20026
#define PM_STR 0x20027
#define RADIXCHAR 0x10000
#define THOUSEP 0x10001
#define YESEXPR 0x50000
#define NOEXPR 0x50001
#define CRNCYSTR 0x40000

__BEGIN_DECLS
char *nl_langinfo(nl_item);
__END_DECLS

#endif
