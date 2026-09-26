#ifndef _FEATURES_H
#define _FEATURES_H
/* glibc-compatibility shim: some third-party headers (libstdc++'s
   os_defines.h among them) include <features.h> unconditionally. We are
   not glibc, so the version test macros always say "no". */
#include <bits/features.h>
#define __GLIBC_PREREQ(maj, min) 0
#define __GLIBC_USE(feature) 0
#endif
