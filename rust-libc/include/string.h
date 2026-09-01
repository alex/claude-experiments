#ifndef _STRING_H
#define _STRING_H
#include <bits/features.h>

#define __NEED_size_t
#include <bits/alltypes.h>

#ifdef __cplusplus
#define NULL 0L
#else
#define NULL ((void *)0)
#endif

__BEGIN_DECLS

void *memcpy(void *__RESTRICT, const void *__RESTRICT, size_t);
void *memmove(void *, const void *, size_t);
void *memset(void *, int, size_t);
int memcmp(const void *, const void *, size_t);
size_t strlen(const char *);

__END_DECLS

#endif
