#include <bits/features.h>

#undef assert
#ifdef NDEBUG
#define assert(x) ((void)0)
#else
#define assert(x) ((x) ? (void)0 : __assert_fail(#x, __FILE__, __LINE__, __func__))
#endif

#if __STDC_VERSION__ >= 201112L && __STDC_VERSION__ < 202311L && !defined(__cplusplus)
#define static_assert _Static_assert
#endif

__BEGIN_DECLS
__NORETURN void __assert_fail(const char *, const char *, int, const char *);
__END_DECLS
