#ifndef _SYS_FILE_H
#define _SYS_FILE_H
#include <bits/features.h>

#define LOCK_SH 1
#define LOCK_EX 2
#define LOCK_NB 4
#define LOCK_UN 8

__BEGIN_DECLS
int flock(int, int);
__END_DECLS

#endif
