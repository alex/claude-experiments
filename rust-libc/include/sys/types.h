#ifndef _SYS_TYPES_H
#define _SYS_TYPES_H

#define __NEED_size_t
#define __NEED_ssize_t
#define __NEED_off_t
#define __NEED_pid_t
#define __NEED_uid_t
#define __NEED_gid_t
#define __NEED_mode_t
#define __NEED_time_t
#define __NEED_clockid_t
#include <bits/alltypes.h>

typedef unsigned long dev_t;
typedef unsigned long ino_t;
typedef unsigned long nlink_t;
typedef long blksize_t;
typedef long blkcnt_t;
typedef long suseconds_t;
typedef unsigned useconds_t;
typedef int id_t;
typedef int key_t;
typedef unsigned int u_int;
typedef unsigned long u_long;
typedef unsigned char u_char;
typedef unsigned short u_short;
typedef long loff_t;
typedef unsigned long fsblkcnt_t;
typedef unsigned long fsfilcnt_t;

#endif
