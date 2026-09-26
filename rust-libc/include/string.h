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
void *memchr(const void *, int, size_t);
void *memrchr(const void *, int, size_t);
void *memccpy(void *__RESTRICT, const void *__RESTRICT, int, size_t);
void *memmem(const void *, size_t, const void *, size_t);

char *strcpy(char *__RESTRICT, const char *__RESTRICT);
char *strncpy(char *__RESTRICT, const char *__RESTRICT, size_t);
char *stpcpy(char *__RESTRICT, const char *__RESTRICT);
char *stpncpy(char *__RESTRICT, const char *__RESTRICT, size_t);
char *strcat(char *__RESTRICT, const char *__RESTRICT);
char *strncat(char *__RESTRICT, const char *__RESTRICT, size_t);
size_t strlcpy(char *__RESTRICT, const char *__RESTRICT, size_t);
size_t strlcat(char *__RESTRICT, const char *__RESTRICT, size_t);

int strcmp(const char *, const char *);
int strncmp(const char *, const char *, size_t);
int strcoll(const char *, const char *);
size_t strxfrm(char *__RESTRICT, const char *__RESTRICT, size_t);

char *strchr(const char *, int);
char *strrchr(const char *, int);
char *strchrnul(const char *, int);
size_t strcspn(const char *, const char *);
size_t strspn(const char *, const char *);
char *strpbrk(const char *, const char *);
char *strstr(const char *, const char *);
char *strtok(char *__RESTRICT, const char *__RESTRICT);
char *strtok_r(char *__RESTRICT, const char *__RESTRICT, char **__RESTRICT);
char *strsep(char **, const char *);

size_t strlen(const char *);
size_t strnlen(const char *, size_t);
char *strerror(int);
int strerror_r(int, char *, size_t);
char *strdup(const char *);
char *strndup(const char *, size_t);
char *strsignal(int);

__END_DECLS

#endif
