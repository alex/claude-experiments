#ifndef _SYS_SENDFILE_H
#define _SYS_SENDFILE_H
#include <bits/features.h>
#include <sys/types.h>

__BEGIN_DECLS
ssize_t sendfile(int, int, off_t *, size_t);
__END_DECLS

#endif
