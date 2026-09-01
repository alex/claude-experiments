#ifndef _SYS_STATFS_H
#define _SYS_STATFS_H
#include <bits/features.h>

#define __NEED_size_t
#include <bits/alltypes.h>

typedef struct { int __val[2]; } fsid_t;

struct statfs {
    unsigned long f_type;
    unsigned long f_bsize;
    unsigned long long f_blocks;
    unsigned long long f_bfree;
    unsigned long long f_bavail;
    unsigned long long f_files;
    unsigned long long f_ffree;
    fsid_t f_fsid;
    unsigned long f_namelen;
    unsigned long f_frsize;
    unsigned long f_flags;
    unsigned long f_spare[4];
};

#define ST_RDONLY 1
#define ST_NOSUID 2
#define ST_NODEV 4
#define ST_NOEXEC 8
#define ST_SYNCHRONOUS 16
#define ST_MANDLOCK 64
#define ST_NOATIME 1024
#define ST_NODIRATIME 2048
#define ST_RELATIME 4096

__BEGIN_DECLS
int statfs(const char *, struct statfs *);
int fstatfs(int, struct statfs *);
__END_DECLS

#endif
