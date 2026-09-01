#ifndef _STDDEF_H
#define _STDDEF_H

#define __NEED_size_t
#define __NEED_ptrdiff_t
#define __NEED_wchar_t
#include <bits/alltypes.h>

#ifdef __cplusplus
#define NULL 0L
#else
#define NULL ((void *)0)
#endif

#define offsetof(type, member) __builtin_offsetof(type, member)

#if __STDC_VERSION__ >= 201112L
typedef struct { long long __ll; long double __ld; } max_align_t;
#endif

#endif
