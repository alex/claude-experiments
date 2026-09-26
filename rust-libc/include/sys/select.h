#ifndef _SYS_SELECT_H
#define _SYS_SELECT_H
#include <bits/features.h>

#define __NEED_struct_timespec
#define __NEED_time_t
#define __NEED_sigset_t
#include <bits/alltypes.h>
#include <sys/time.h>

#define FD_SETSIZE 1024
typedef unsigned long fd_mask;
typedef struct { unsigned long fds_bits[FD_SETSIZE / (8 * sizeof(long))]; } fd_set;

#define FD_ZERO(s) do { unsigned long *__p = (s)->fds_bits; for (unsigned __i = 0; __i < sizeof(fd_set) / sizeof(long); __i++) __p[__i] = 0; } while (0)
#define FD_SET(d, s) ((s)->fds_bits[(d) / (8 * sizeof(long))] |= (1UL << ((d) % (8 * sizeof(long)))))
#define FD_CLR(d, s) ((s)->fds_bits[(d) / (8 * sizeof(long))] &= ~(1UL << ((d) % (8 * sizeof(long)))))
#define FD_ISSET(d, s) (!!((s)->fds_bits[(d) / (8 * sizeof(long))] & (1UL << ((d) % (8 * sizeof(long))))))

__BEGIN_DECLS
int select(int, fd_set *__RESTRICT, fd_set *__RESTRICT, fd_set *__RESTRICT, struct timeval *__RESTRICT);
int pselect(int, fd_set *__RESTRICT, fd_set *__RESTRICT, fd_set *__RESTRICT, const struct timespec *__RESTRICT, const sigset_t *__RESTRICT);
__END_DECLS

#endif
