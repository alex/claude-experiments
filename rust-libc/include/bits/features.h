/* Common macros shared by every header. */
#ifndef _BITS_FEATURES_H
#define _BITS_FEATURES_H

#ifdef __cplusplus
#define __BEGIN_DECLS extern "C" {
#define __END_DECLS }
#else
#define __BEGIN_DECLS
#define __END_DECLS
#endif

#ifdef __cplusplus
#define __NORETURN __attribute__((__noreturn__))
#define __RESTRICT __restrict
#else
#define __NORETURN _Noreturn
#define __RESTRICT restrict
#endif

#endif
