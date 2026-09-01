#ifndef _WCHAR_H
#define _WCHAR_H
#include <bits/features.h>

#define __NEED_size_t
#define __NEED_wchar_t
#include <bits/alltypes.h>
#include <stdarg.h>

typedef unsigned wint_t;
typedef struct { unsigned __state; } mbstate_t;
typedef struct _IO_FILE FILE;

#define WEOF 0xffffffffU
#define WCHAR_MIN (-1 - 0x7fffffff)
#define WCHAR_MAX 0x7fffffff

#ifdef __cplusplus
#define NULL 0L
#else
#define NULL ((void *)0)
#endif

__BEGIN_DECLS

size_t mbrtowc(wchar_t *__RESTRICT, const char *__RESTRICT, size_t, mbstate_t *__RESTRICT);
size_t wcrtomb(char *__RESTRICT, wchar_t, mbstate_t *__RESTRICT);
size_t mbrlen(const char *__RESTRICT, size_t, mbstate_t *__RESTRICT);
int mbsinit(const mbstate_t *);
size_t mbsrtowcs(wchar_t *__RESTRICT, const char **__RESTRICT, size_t, mbstate_t *__RESTRICT);
size_t wcsrtombs(char *__RESTRICT, const wchar_t **__RESTRICT, size_t, mbstate_t *__RESTRICT);
wint_t btowc(int);
int wctob(wint_t);

size_t wcslen(const wchar_t *);
size_t wcsnlen(const wchar_t *, size_t);
wchar_t *wcscpy(wchar_t *__RESTRICT, const wchar_t *__RESTRICT);
wchar_t *wcsncpy(wchar_t *__RESTRICT, const wchar_t *__RESTRICT, size_t);
wchar_t *wcscat(wchar_t *__RESTRICT, const wchar_t *__RESTRICT);
wchar_t *wcsncat(wchar_t *__RESTRICT, const wchar_t *__RESTRICT, size_t);
int wcscmp(const wchar_t *, const wchar_t *);
int wcsncmp(const wchar_t *, const wchar_t *, size_t);
int wcscoll(const wchar_t *, const wchar_t *);
size_t wcsxfrm(wchar_t *__RESTRICT, const wchar_t *__RESTRICT, size_t);
int wcscasecmp(const wchar_t *, const wchar_t *);
int wcsncasecmp(const wchar_t *, const wchar_t *, size_t);
wchar_t *wcschr(const wchar_t *, wchar_t);
wchar_t *wcsrchr(const wchar_t *, wchar_t);
wchar_t *wcsstr(const wchar_t *, const wchar_t *);
wchar_t *wcspbrk(const wchar_t *, const wchar_t *);
size_t wcsspn(const wchar_t *, const wchar_t *);
size_t wcscspn(const wchar_t *, const wchar_t *);
wchar_t *wcstok(wchar_t *__RESTRICT, const wchar_t *__RESTRICT, wchar_t **__RESTRICT);
wchar_t *wcsdup(const wchar_t *);
wchar_t *wmemchr(const wchar_t *, wchar_t, size_t);
int wmemcmp(const wchar_t *, const wchar_t *, size_t);
wchar_t *wmemcpy(wchar_t *__RESTRICT, const wchar_t *__RESTRICT, size_t);
wchar_t *wmemmove(wchar_t *, const wchar_t *, size_t);
wchar_t *wmemset(wchar_t *, wchar_t, size_t);
int wcwidth(wchar_t);
int wcswidth(const wchar_t *, size_t);

long wcstol(const wchar_t *__RESTRICT, wchar_t **__RESTRICT, int);
unsigned long wcstoul(const wchar_t *__RESTRICT, wchar_t **__RESTRICT, int);
long long wcstoll(const wchar_t *__RESTRICT, wchar_t **__RESTRICT, int);
unsigned long long wcstoull(const wchar_t *__RESTRICT, wchar_t **__RESTRICT, int);
double wcstod(const wchar_t *__RESTRICT, wchar_t **__RESTRICT);
float wcstof(const wchar_t *__RESTRICT, wchar_t **__RESTRICT);

wint_t fputwc(wchar_t, FILE *);
wint_t putwc(wchar_t, FILE *);
wint_t putwchar(wchar_t);
int fputws(const wchar_t *__RESTRICT, FILE *__RESTRICT);
wint_t fgetwc(FILE *);
wint_t getwc(FILE *);
wint_t getwchar(void);
wchar_t *fgetws(wchar_t *__RESTRICT, int, FILE *__RESTRICT);
int fwide(FILE *, int);
int swprintf(wchar_t *__RESTRICT, size_t, const wchar_t *__RESTRICT, ...);
int vswprintf(wchar_t *__RESTRICT, size_t, const wchar_t *__RESTRICT, va_list);

wint_t towupper(wint_t);
wint_t towlower(wint_t);
int iswalpha(wint_t);
int iswdigit(wint_t);
int iswalnum(wint_t);
int iswspace(wint_t);
int iswupper(wint_t);
int iswlower(wint_t);

__END_DECLS

#endif
