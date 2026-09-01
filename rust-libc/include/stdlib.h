#ifndef _STDLIB_H
#define _STDLIB_H
#include <bits/features.h>

#define __NEED_size_t
#define __NEED_wchar_t
#include <bits/alltypes.h>

#ifdef __cplusplus
#define NULL 0L
#else
#define NULL ((void *)0)
#endif

#define EXIT_SUCCESS 0
#define EXIT_FAILURE 1

__BEGIN_DECLS

__NORETURN void exit(int);
__NORETURN void _Exit(int);
__NORETURN void abort(void);
int atexit(void (*)(void));

__END_DECLS

#endif
