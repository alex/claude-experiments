/* Basic scalar typedefs. Each is guarded so headers can pull in only the
   names they are required to define. */
#ifndef _BITS_ALLTYPES_H
#define _BITS_ALLTYPES_H

#define __NEED_size_t
#endif

#if defined(__NEED_size_t) && !defined(__DEFINED_size_t)
typedef __SIZE_TYPE__ size_t;
#define __DEFINED_size_t
#endif

#if defined(__NEED_ssize_t) && !defined(__DEFINED_ssize_t)
typedef long ssize_t;
#define __DEFINED_ssize_t
#endif

#if defined(__NEED_ptrdiff_t) && !defined(__DEFINED_ptrdiff_t)
typedef __PTRDIFF_TYPE__ ptrdiff_t;
#define __DEFINED_ptrdiff_t
#endif

#if defined(__NEED_wchar_t) && !defined(__DEFINED_wchar_t) && !defined(__cplusplus)
typedef __WCHAR_TYPE__ wchar_t;
#define __DEFINED_wchar_t
#endif

#if defined(__NEED_off_t) && !defined(__DEFINED_off_t)
typedef long off_t;
#define __DEFINED_off_t
#endif

#if defined(__NEED_pid_t) && !defined(__DEFINED_pid_t)
typedef int pid_t;
#define __DEFINED_pid_t
#endif

#if defined(__NEED_uid_t) && !defined(__DEFINED_uid_t)
typedef unsigned uid_t;
#define __DEFINED_uid_t
#endif

#if defined(__NEED_gid_t) && !defined(__DEFINED_gid_t)
typedef unsigned gid_t;
#define __DEFINED_gid_t
#endif

#if defined(__NEED_mode_t) && !defined(__DEFINED_mode_t)
typedef unsigned mode_t;
#define __DEFINED_mode_t
#endif

#if defined(__NEED_time_t) && !defined(__DEFINED_time_t)
typedef long time_t;
#define __DEFINED_time_t
#endif

#if defined(__NEED_clockid_t) && !defined(__DEFINED_clockid_t)
typedef int clockid_t;
#define __DEFINED_clockid_t
#endif

#if defined(__NEED_struct_timespec) && !defined(__DEFINED_struct_timespec)
struct timespec { long tv_sec; long tv_nsec; };
#define __DEFINED_struct_timespec
#endif
