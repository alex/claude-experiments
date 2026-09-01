#ifndef _SYS_EVENTFD_H
#define _SYS_EVENTFD_H
#include <bits/features.h>
#include <stdint.h>

typedef uint64_t eventfd_t;
#define EFD_SEMAPHORE 1
#define EFD_CLOEXEC 02000000
#define EFD_NONBLOCK 04000

__BEGIN_DECLS
int eventfd(unsigned, int);
__END_DECLS

#endif
