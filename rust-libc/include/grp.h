#ifndef _GRP_H
#define _GRP_H
#include <bits/features.h>

#define __NEED_size_t
#define __NEED_gid_t
#include <bits/alltypes.h>

struct group {
    char *gr_name;
    char *gr_passwd;
    gid_t gr_gid;
    char **gr_mem;
};

__BEGIN_DECLS
struct group *getgrnam(const char *);
struct group *getgrgid(gid_t);
int getgrnam_r(const char *, struct group *, char *, size_t, struct group **);
int getgrgid_r(gid_t, struct group *, char *, size_t, struct group **);
__END_DECLS

#endif
