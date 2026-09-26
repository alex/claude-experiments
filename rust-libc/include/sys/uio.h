#ifndef _SYS_UIO_H
#define _SYS_UIO_H
#include <bits/features.h>
#include <sys/types.h>

struct iovec {
    void *iov_base;
    size_t iov_len;
};

#define UIO_MAXIOV 1024

__BEGIN_DECLS
ssize_t readv(int, const struct iovec *, int);
ssize_t writev(int, const struct iovec *, int);
ssize_t preadv(int, const struct iovec *, int, off_t);
ssize_t pwritev(int, const struct iovec *, int, off_t);
__END_DECLS

#endif
