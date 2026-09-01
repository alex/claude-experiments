#ifndef _LIMITS_H
#define _LIMITS_H

#define CHAR_BIT 8
#define SCHAR_MIN (-128)
#define SCHAR_MAX 127
#define UCHAR_MAX 255
#ifdef __CHAR_UNSIGNED__
#define CHAR_MIN 0
#define CHAR_MAX 255
#else
#define CHAR_MIN (-128)
#define CHAR_MAX 127
#endif
#define MB_LEN_MAX 4
#define SHRT_MIN (-1 - 0x7fff)
#define SHRT_MAX 0x7fff
#define USHRT_MAX 0xffff
#define INT_MIN (-1 - 0x7fffffff)
#define INT_MAX 0x7fffffff
#define UINT_MAX 0xffffffffU
#define LONG_MIN (-LONG_MAX - 1)
#define LONG_MAX 0x7fffffffffffffffL
#define ULONG_MAX (2UL * LONG_MAX + 1)
#define LLONG_MIN (-LLONG_MAX - 1)
#define LLONG_MAX 0x7fffffffffffffffLL
#define ULLONG_MAX (2ULL * LLONG_MAX + 1)

#define PATH_MAX 4096
#define NAME_MAX 255
#define PIPE_BUF 4096
#define ARG_MAX 131072
#define IOV_MAX 1024
#define SSIZE_MAX LONG_MAX
#define PTHREAD_STACK_MIN 16384
#define PTHREAD_KEYS_MAX 128
#define PTHREAD_DESTRUCTOR_ITERATIONS 4
#define ATEXIT_MAX 64
#define HOST_NAME_MAX 64
#define LOGIN_NAME_MAX 256
#define TTY_NAME_MAX 32
#define NL_ARGMAX 9

#endif
