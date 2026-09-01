#ifndef _MALLOC_H
#define _MALLOC_H
#include <bits/features.h>

#define __NEED_size_t
#include <bits/alltypes.h>

__BEGIN_DECLS

void *malloc(size_t);
void *calloc(size_t, size_t);
void *realloc(void *, size_t);
void free(void *);
void *memalign(size_t, size_t);
void *valloc(size_t);
size_t malloc_usable_size(void *);

__END_DECLS

#endif
