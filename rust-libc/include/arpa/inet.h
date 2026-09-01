#ifndef _ARPA_INET_H
#define _ARPA_INET_H
#include <bits/features.h>
#include <netinet/in.h>

__BEGIN_DECLS
int inet_pton(int, const char *__RESTRICT, void *__RESTRICT);
const char *inet_ntop(int, const void *__RESTRICT, char *__RESTRICT, socklen_t);
int inet_aton(const char *, struct in_addr *);
in_addr_t inet_addr(const char *);
char *inet_ntoa(struct in_addr);
__END_DECLS

#endif
