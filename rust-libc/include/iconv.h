#ifndef _ICONV_H
#define _ICONV_H
#include <bits/features.h>

#define __NEED_size_t
#include <bits/alltypes.h>

typedef void *iconv_t;

__BEGIN_DECLS
iconv_t iconv_open(const char *, const char *);
size_t iconv(iconv_t, char **__RESTRICT, size_t *__RESTRICT, char **__RESTRICT, size_t *__RESTRICT);
int iconv_close(iconv_t);
__END_DECLS

#endif
