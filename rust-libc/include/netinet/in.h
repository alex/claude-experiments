#ifndef _NETINET_IN_H
#define _NETINET_IN_H
#include <bits/features.h>
#include <stdint.h>
#include <sys/socket.h>

typedef uint16_t in_port_t;
typedef uint32_t in_addr_t;
struct in_addr { in_addr_t s_addr; };
struct in6_addr {
    union {
        uint8_t __s6_addr[16];
        uint16_t __s6_addr16[8];
        uint32_t __s6_addr32[4];
    } __in6_union;
};
#define s6_addr __in6_union.__s6_addr
#define s6_addr16 __in6_union.__s6_addr16
#define s6_addr32 __in6_union.__s6_addr32

struct sockaddr_in {
    sa_family_t sin_family;
    in_port_t sin_port;
    struct in_addr sin_addr;
    uint8_t sin_zero[8];
};

struct sockaddr_in6 {
    sa_family_t sin6_family;
    in_port_t sin6_port;
    uint32_t sin6_flowinfo;
    struct in6_addr sin6_addr;
    uint32_t sin6_scope_id;
};

struct ipv6_mreq {
    struct in6_addr ipv6mr_multiaddr;
    unsigned ipv6mr_interface;
};

struct ip_mreq {
    struct in_addr imr_multiaddr;
    struct in_addr imr_interface;
};

#define INADDR_ANY ((in_addr_t)0x00000000)
#define INADDR_BROADCAST ((in_addr_t)0xffffffff)
#define INADDR_NONE ((in_addr_t)0xffffffff)
#define INADDR_LOOPBACK ((in_addr_t)0x7f000001)
#define IN6ADDR_ANY_INIT {{{0}}}
#define IN6ADDR_LOOPBACK_INIT {{{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1}}}
#define INET_ADDRSTRLEN 16
#define INET6_ADDRSTRLEN 46

extern const struct in6_addr in6addr_any, in6addr_loopback;

#define IPPROTO_IP 0
#define IPPROTO_ICMP 1
#define IPPROTO_TCP 6
#define IPPROTO_UDP 17
#define IPPROTO_IPV6 41
#define IPPROTO_ICMPV6 58
#define IPPROTO_RAW 255

#define IP_TOS 1
#define IP_TTL 2
#define IP_HDRINCL 3
#define IP_OPTIONS 4
#define IP_PKTINFO 8
#define IP_MULTICAST_IF 32
#define IP_MULTICAST_TTL 33
#define IP_MULTICAST_LOOP 34
#define IP_ADD_MEMBERSHIP 35
#define IP_DROP_MEMBERSHIP 36
#define IPV6_UNICAST_HOPS 16
#define IPV6_MULTICAST_IF 17
#define IPV6_MULTICAST_HOPS 18
#define IPV6_MULTICAST_LOOP 19
#define IPV6_JOIN_GROUP 20
#define IPV6_LEAVE_GROUP 21
#define IPV6_V6ONLY 26
#define IPV6_RECVPKTINFO 49
#define IPV6_PKTINFO 50

#define IN6_IS_ADDR_UNSPECIFIED(a) (((a)->s6_addr32[0] | (a)->s6_addr32[1] | (a)->s6_addr32[2] | (a)->s6_addr32[3]) == 0)
#define IN6_IS_ADDR_LOOPBACK(a) ((a)->s6_addr32[0] == 0 && (a)->s6_addr32[1] == 0 && (a)->s6_addr32[2] == 0 && (a)->s6_addr[12] == 0 && (a)->s6_addr[13] == 0 && (a)->s6_addr[14] == 0 && (a)->s6_addr[15] == 1)
#define IN6_IS_ADDR_V4MAPPED(a) ((a)->s6_addr32[0] == 0 && (a)->s6_addr32[1] == 0 && (a)->s6_addr[8] == 0 && (a)->s6_addr[9] == 0 && (a)->s6_addr[10] == 0xff && (a)->s6_addr[11] == 0xff)
#define IN6_IS_ADDR_MULTICAST(a) ((a)->s6_addr[0] == 0xff)
#define IN6_IS_ADDR_LINKLOCAL(a) ((a)->s6_addr[0] == 0xfe && ((a)->s6_addr[1] & 0xc0) == 0x80)

__BEGIN_DECLS
uint16_t htons(uint16_t);
uint16_t ntohs(uint16_t);
uint32_t htonl(uint32_t);
uint32_t ntohl(uint32_t);
__END_DECLS

#endif
