#ifndef _DLFCN_H
#define _DLFCN_H
#include <bits/features.h>

#define RTLD_LAZY 1
#define RTLD_NOW 2
#define RTLD_NOLOAD 4
#define RTLD_NODELETE 4096
#define RTLD_GLOBAL 256
#define RTLD_LOCAL 0
#define RTLD_NEXT ((void *)-1)
#define RTLD_DEFAULT ((void *)0)

__BEGIN_DECLS
void *dlopen(const char *, int);
void *dlsym(void *__RESTRICT, const char *__RESTRICT);
int dlclose(void *);
char *dlerror(void);
__END_DECLS

#endif
