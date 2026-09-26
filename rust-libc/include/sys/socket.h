#ifndef _SYS_SOCKET_H
#define _SYS_SOCKET_H
#include <bits/features.h>
#include <sys/types.h>
#include <sys/uio.h>

typedef unsigned socklen_t;
typedef unsigned short sa_family_t;

struct sockaddr {
    sa_family_t sa_family;
    char sa_data[14];
};

struct sockaddr_storage {
    sa_family_t ss_family;
    char __ss_padding[128 - sizeof(long) - sizeof(sa_family_t)];
    unsigned long __ss_align;
};

struct msghdr {
    void *msg_name;
    socklen_t msg_namelen;
    struct iovec *msg_iov;
    size_t msg_iovlen;
    void *msg_control;
    size_t msg_controllen;
    int msg_flags;
};

struct cmsghdr {
    size_t cmsg_len;
    int cmsg_level;
    int cmsg_type;
};

struct linger {
    int l_onoff;
    int l_linger;
};

struct ucred {
    pid_t pid;
    uid_t uid;
    gid_t gid;
};

#define CMSG_ALIGN(len) (((len) + sizeof(size_t) - 1) & ~(sizeof(size_t) - 1))
#define CMSG_SPACE(len) (CMSG_ALIGN(len) + CMSG_ALIGN(sizeof(struct cmsghdr)))
#define CMSG_LEN(len) (CMSG_ALIGN(sizeof(struct cmsghdr)) + (len))
#define CMSG_DATA(cmsg) ((unsigned char *)(((struct cmsghdr *)(cmsg)) + 1))
#define CMSG_FIRSTHDR(mhdr) ((size_t)(mhdr)->msg_controllen >= sizeof(struct cmsghdr) ? (struct cmsghdr *)(mhdr)->msg_control : (struct cmsghdr *)0)
#define __CMSG_NEXT(cmsg) ((unsigned char *)(cmsg) + CMSG_ALIGN((cmsg)->cmsg_len))
#define __MHDR_END(mhdr) ((unsigned char *)(mhdr)->msg_control + (mhdr)->msg_controllen)
#define CMSG_NXTHDR(mhdr, cmsg) ((cmsg)->cmsg_len < sizeof(struct cmsghdr) || \
    (size_t)(__MHDR_END(mhdr) - __CMSG_NEXT(cmsg)) < sizeof(struct cmsghdr) ? (struct cmsghdr *)0 : (struct cmsghdr *)__CMSG_NEXT(cmsg))

#define SCM_RIGHTS 1
#define SCM_CREDENTIALS 2

#define AF_UNSPEC 0
#define AF_UNIX 1
#define AF_LOCAL 1
#define AF_INET 2
#define AF_INET6 10
#define AF_NETLINK 16
#define AF_PACKET 17
#define PF_UNSPEC AF_UNSPEC
#define PF_UNIX AF_UNIX
#define PF_LOCAL AF_LOCAL
#define PF_INET AF_INET
#define PF_INET6 AF_INET6
#define PF_NETLINK AF_NETLINK
#define PF_PACKET AF_PACKET

#define SOCK_STREAM 1
#define SOCK_DGRAM 2
#define SOCK_RAW 3
#define SOCK_RDM 4
#define SOCK_SEQPACKET 5
#define SOCK_NONBLOCK 04000
#define SOCK_CLOEXEC 02000000

#define SOL_SOCKET 1
#define SO_DEBUG 1
#define SO_REUSEADDR 2
#define SO_TYPE 3
#define SO_ERROR 4
#define SO_DONTROUTE 5
#define SO_BROADCAST 6
#define SO_SNDBUF 7
#define SO_RCVBUF 8
#define SO_KEEPALIVE 9
#define SO_OOBINLINE 10
#define SO_LINGER 13
#define SO_REUSEPORT 15
#define SO_PASSCRED 16
#define SO_PEERCRED 17
#define SO_RCVLOWAT 18
#define SO_SNDLOWAT 19
#define SO_RCVTIMEO 20
#define SO_SNDTIMEO 21
#define SO_BINDTODEVICE 25
#define SO_ACCEPTCONN 30
#define SO_PROTOCOL 38
#define SO_DOMAIN 39

#define MSG_OOB 1
#define MSG_PEEK 2
#define MSG_DONTROUTE 4
#define MSG_CTRUNC 8
#define MSG_TRUNC 0x20
#define MSG_DONTWAIT 0x40
#define MSG_EOR 0x80
#define MSG_WAITALL 0x100
#define MSG_NOSIGNAL 0x4000
#define MSG_CMSG_CLOEXEC 0x40000000

#define SHUT_RD 0
#define SHUT_WR 1
#define SHUT_RDWR 2
#define SOMAXCONN 4096

__BEGIN_DECLS
int socket(int, int, int);
int socketpair(int, int, int, int[2]);
int bind(int, const struct sockaddr *, socklen_t);
int listen(int, int);
int accept(int, struct sockaddr *__RESTRICT, socklen_t *__RESTRICT);
int accept4(int, struct sockaddr *__RESTRICT, socklen_t *__RESTRICT, int);
int connect(int, const struct sockaddr *, socklen_t);
ssize_t send(int, const void *, size_t, int);
ssize_t sendto(int, const void *, size_t, int, const struct sockaddr *, socklen_t);
ssize_t sendmsg(int, const struct msghdr *, int);
ssize_t recv(int, void *, size_t, int);
ssize_t recvfrom(int, void *__RESTRICT, size_t, int, struct sockaddr *__RESTRICT, socklen_t *__RESTRICT);
ssize_t recvmsg(int, struct msghdr *, int);
int shutdown(int, int);
int getsockname(int, struct sockaddr *__RESTRICT, socklen_t *__RESTRICT);
int getpeername(int, struct sockaddr *__RESTRICT, socklen_t *__RESTRICT);
int setsockopt(int, int, int, const void *, socklen_t);
int getsockopt(int, int, int, void *__RESTRICT, socklen_t *__RESTRICT);
__END_DECLS

#endif
