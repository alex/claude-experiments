#ifndef _POLL_H
#define _POLL_H
#include <bits/features.h>

#define __NEED_struct_timespec
#define __NEED_time_t
#define __NEED_sigset_t
#include <bits/alltypes.h>

typedef unsigned long nfds_t;
struct pollfd {
    int fd;
    short events;
    short revents;
};

#define POLLIN 0x001
#define POLLPRI 0x002
#define POLLOUT 0x004
#define POLLERR 0x008
#define POLLHUP 0x010
#define POLLNVAL 0x020
#define POLLRDNORM 0x040
#define POLLRDBAND 0x080
#define POLLWRNORM 0x100
#define POLLWRBAND 0x200
#define POLLMSG 0x400
#define POLLRDHUP 0x2000

__BEGIN_DECLS
int poll(struct pollfd *, nfds_t, int);
int ppoll(struct pollfd *, nfds_t, const struct timespec *, const sigset_t *);
__END_DECLS

#endif
