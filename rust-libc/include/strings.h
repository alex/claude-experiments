#ifndef _STRINGS_H
#define _STRINGS_H
#include <bits/features.h>

#define __NEED_size_t
#include <bits/alltypes.h>

__BEGIN_DECLS

int bcmp(const void *, const void *, size_t);
void bcopy(const void *, void *, size_t);
void bzero(void *, size_t);
void explicit_bzero(void *, size_t);
int strcasecmp(const char *, const char *);
int strncasecmp(const char *, const char *, size_t);
int ffs(int);
int ffsl(long);
int ffsll(long long);

__END_DECLS

#endif
