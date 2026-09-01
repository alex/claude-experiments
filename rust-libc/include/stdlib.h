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
#define RAND_MAX 0x7fffffff
#define MB_CUR_MAX 4

typedef struct { int quot, rem; } div_t;
typedef struct { long quot, rem; } ldiv_t;
typedef struct { long long quot, rem; } lldiv_t;

__BEGIN_DECLS

int atoi(const char *);
long atol(const char *);
long long atoll(const char *);
double atof(const char *);
long strtol(const char *__RESTRICT, char **__RESTRICT, int);
unsigned long strtoul(const char *__RESTRICT, char **__RESTRICT, int);
long long strtoll(const char *__RESTRICT, char **__RESTRICT, int);
unsigned long long strtoull(const char *__RESTRICT, char **__RESTRICT, int);
double strtod(const char *__RESTRICT, char **__RESTRICT);
float strtof(const char *__RESTRICT, char **__RESTRICT);

int rand(void);
void srand(unsigned);
int rand_r(unsigned *);
long random(void);
void srandom(unsigned);

char *getenv(const char *);
int setenv(const char *, const char *, int);
int unsetenv(const char *);
int putenv(char *);
int clearenv(void);

void qsort(void *, size_t, size_t, int (*)(const void *, const void *));
void qsort_r(void *, size_t, size_t, int (*)(const void *, const void *, void *), void *);
void *bsearch(const void *, const void *, size_t, size_t, int (*)(const void *, const void *));

int abs(int);
long labs(long);
long long llabs(long long);
div_t div(int, int);
ldiv_t ldiv(long, long);
lldiv_t lldiv(long long, long long);

__NORETURN void exit(int);
__NORETURN void _Exit(int);
__NORETURN void abort(void);
int atexit(void (*)(void));
int system(const char *);
char *realpath(const char *__RESTRICT, char *__RESTRICT);
int mkstemp(char *);
int mkostemp(char *, int);
char *mkdtemp(char *);

void *malloc(size_t);
void *calloc(size_t, size_t);
void *realloc(void *, size_t);
void *reallocarray(void *, size_t, size_t);
void free(void *);
void *aligned_alloc(size_t, size_t);
int posix_memalign(void **, size_t, size_t);
void *memalign(size_t, size_t);
void *valloc(size_t);

__END_DECLS

#endif
