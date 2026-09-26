#ifndef _DIRENT_H
#define _DIRENT_H
#include <bits/features.h>

#define __NEED_size_t
#define __NEED_ssize_t
#define __NEED_off_t
#include <bits/alltypes.h>

typedef struct __dirstream DIR;
typedef unsigned long ino_t;

struct dirent {
    ino_t d_ino;
    off_t d_off;
    unsigned short d_reclen;
    unsigned char d_type;
    char d_name[256];
};

#define DT_UNKNOWN 0
#define DT_FIFO 1
#define DT_CHR 2
#define DT_DIR 4
#define DT_BLK 6
#define DT_REG 8
#define DT_LNK 10
#define DT_SOCK 12
#define DT_WHT 14

__BEGIN_DECLS
DIR *opendir(const char *);
DIR *fdopendir(int);
int closedir(DIR *);
struct dirent *readdir(DIR *);
int readdir_r(DIR *__RESTRICT, struct dirent *__RESTRICT, struct dirent **__RESTRICT);
void rewinddir(DIR *);
long telldir(DIR *);
void seekdir(DIR *, long);
int dirfd(DIR *);
int scandir(const char *, struct dirent ***, int (*)(const struct dirent *), int (*)(const struct dirent **, const struct dirent **));
int alphasort(const struct dirent **, const struct dirent **);
__END_DECLS

#endif
