#ifndef _WCHAR_H
#define _WCHAR_H
#include <bits/features.h>

#define __NEED_size_t
#define __NEED_wchar_t
#include <bits/alltypes.h>

typedef unsigned wint_t;
typedef struct { unsigned __state; } mbstate_t;

#define WEOF 0xffffffffU
#define WCHAR_MIN (-1 - 0x7fffffff)
#define WCHAR_MAX 0x7fffffff

#ifdef __cplusplus
#define NULL 0L
#else
#define NULL ((void *)0)
#endif

#endif
