#ifndef _STDIO_H
#define _STDIO_H
#include <bits/features.h>

#define __NEED_size_t
#define __NEED_ssize_t
#define __NEED_off_t
#include <bits/alltypes.h>
#include <stdarg.h>

#ifdef __cplusplus
#define NULL 0L
#else
#define NULL ((void *)0)
#endif

typedef struct _IO_FILE FILE;
typedef long fpos_t;

#define EOF (-1)
#define BUFSIZ 8192
#define FILENAME_MAX 4096
#define FOPEN_MAX 1000
#define TMP_MAX 10000
#define L_tmpnam 20
#define P_tmpdir "/tmp"
#define L_ctermid 20

#define _IOFBF 0
#define _IOLBF 1
#define _IONBF 2

#define SEEK_SET 0
#define SEEK_CUR 1
#define SEEK_END 2

__BEGIN_DECLS

extern FILE *stdin;
extern FILE *stdout;
extern FILE *stderr;
#define stdin stdin
#define stdout stdout
#define stderr stderr

FILE *fopen(const char *__RESTRICT, const char *__RESTRICT);
FILE *freopen(const char *__RESTRICT, const char *__RESTRICT, FILE *__RESTRICT);
FILE *fdopen(int, const char *);
FILE *fmemopen(void *__RESTRICT, size_t, const char *__RESTRICT);
FILE *open_memstream(char **, size_t *);
FILE *tmpfile(void);
int fclose(FILE *);
int fflush(FILE *);
int fileno(FILE *);
int remove(const char *);
int rename(const char *, const char *);

void setbuf(FILE *__RESTRICT, char *__RESTRICT);
void setbuffer(FILE *__RESTRICT, char *__RESTRICT, size_t);
void setlinebuf(FILE *);
int setvbuf(FILE *__RESTRICT, char *__RESTRICT, int, size_t);

size_t fread(void *__RESTRICT, size_t, size_t, FILE *__RESTRICT);
size_t fwrite(const void *__RESTRICT, size_t, size_t, FILE *__RESTRICT);

int fgetc(FILE *);
int getc(FILE *);
int getchar(void);
int getc_unlocked(FILE *);
int getchar_unlocked(void);
int ungetc(int, FILE *);
int fputc(int, FILE *);
int putc(int, FILE *);
int putchar(int);
int putc_unlocked(int, FILE *);
int putchar_unlocked(int);
char *fgets(char *__RESTRICT, int, FILE *__RESTRICT);
int fputs(const char *__RESTRICT, FILE *__RESTRICT);
int puts(const char *);
ssize_t getline(char **__RESTRICT, size_t *__RESTRICT, FILE *__RESTRICT);
ssize_t getdelim(char **__RESTRICT, size_t *__RESTRICT, int, FILE *__RESTRICT);

int fseek(FILE *, long, int);
long ftell(FILE *);
int fseeko(FILE *, off_t, int);
off_t ftello(FILE *);
void rewind(FILE *);
int fgetpos(FILE *__RESTRICT, fpos_t *__RESTRICT);
int fsetpos(FILE *, const fpos_t *);

void clearerr(FILE *);
int feof(FILE *);
int ferror(FILE *);
void perror(const char *);

void flockfile(FILE *);
int ftrylockfile(FILE *);
void funlockfile(FILE *);

int printf(const char *__RESTRICT, ...);
int fprintf(FILE *__RESTRICT, const char *__RESTRICT, ...);
int sprintf(char *__RESTRICT, const char *__RESTRICT, ...);
int snprintf(char *__RESTRICT, size_t, const char *__RESTRICT, ...);
int dprintf(int, const char *__RESTRICT, ...);
int asprintf(char **, const char *, ...);
int vprintf(const char *__RESTRICT, va_list);
int vfprintf(FILE *__RESTRICT, const char *__RESTRICT, va_list);
int vsprintf(char *__RESTRICT, const char *__RESTRICT, va_list);
int vsnprintf(char *__RESTRICT, size_t, const char *__RESTRICT, va_list);
int vdprintf(int, const char *__RESTRICT, va_list);
int vasprintf(char **, const char *, va_list);

int scanf(const char *__RESTRICT, ...);
int fscanf(FILE *__RESTRICT, const char *__RESTRICT, ...);
int sscanf(const char *__RESTRICT, const char *__RESTRICT, ...);
int vscanf(const char *__RESTRICT, va_list);
int vfscanf(FILE *__RESTRICT, const char *__RESTRICT, va_list);
int vsscanf(const char *__RESTRICT, const char *__RESTRICT, va_list);

FILE *popen(const char *, const char *);
int pclose(FILE *);
char *ctermid(char *);
char *tmpnam(char *);
__END_DECLS

#endif
