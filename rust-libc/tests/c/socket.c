// Sockets: unix socketpair with fd passing, TCP and UDP over loopback,
// address conversion, getaddrinfo, poll/select/epoll/eventfd.
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <netdb.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <poll.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/epoll.h>
#include <sys/eventfd.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

int main(void) {
    // Address text.
    struct in_addr a4;
    CHECK(inet_pton(AF_INET, "192.168.1.10", &a4) == 1 && ntohl(a4.s_addr) == 0xc0a8010a);
    char text[INET6_ADDRSTRLEN];
    CHECK(inet_ntop(AF_INET, &a4, text, sizeof text) == text && strcmp(text, "192.168.1.10") == 0);
    struct in6_addr a6;
    CHECK(inet_pton(AF_INET6, "2001:db8::ff00:42:8329", &a6) == 1 && a6.s6_addr[0] == 0x20 && a6.s6_addr[15] == 0x29);
    CHECK(inet_ntop(AF_INET6, &a6, text, sizeof text) == text && strcmp(text, "2001:db8::ff00:42:8329") == 0);
    CHECK(inet_pton(AF_INET, "1.2.3", &a4) == 0);
    CHECK(inet_pton(99, "x", &a4) == -1 && errno == EAFNOSUPPORT);
    CHECK(inet_aton("10.0.0.1", &a4) == 1 && strcmp(inet_ntoa(a4), "10.0.0.1") == 0);
    CHECK(inet_addr("bogus") == INADDR_NONE);
    CHECK(htons(0x1234) == 0x3412 && ntohl(htonl(0xdeadbeef)) == 0xdeadbeef);

    // Unix socket pair passing a file descriptor.
    int sv[2];
    CHECK(socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, sv) == 0);
    int pfd[2];
    CHECK(pipe(pfd) == 0);
    struct msghdr msg;
    memset(&msg, 0, sizeof msg);
    char data = 'x';
    struct iovec iov = {&data, 1};
    union { struct cmsghdr h; char buf[CMSG_SPACE(sizeof(int))]; } cbuf;
    memset(&cbuf, 0, sizeof cbuf);
    msg.msg_iov = &iov;
    msg.msg_iovlen = 1;
    msg.msg_control = cbuf.buf;
    msg.msg_controllen = sizeof cbuf.buf;
    struct cmsghdr *cm = CMSG_FIRSTHDR(&msg);
    cm->cmsg_level = SOL_SOCKET;
    cm->cmsg_type = SCM_RIGHTS;
    cm->cmsg_len = CMSG_LEN(sizeof(int));
    memcpy(CMSG_DATA(cm), &pfd[1], sizeof(int));
    CHECK(sendmsg(sv[0], &msg, 0) == 1);
    char got = 0;
    iov.iov_base = &got;
    memset(cbuf.buf, 0, sizeof cbuf.buf);
    CHECK(recvmsg(sv[1], &msg, 0) == 1 && got == 'x');
    cm = CMSG_FIRSTHDR(&msg);
    CHECK(cm && cm->cmsg_type == SCM_RIGHTS);
    int received;
    memcpy(&received, CMSG_DATA(cm), sizeof(int));
    CHECK(received != pfd[1] && write(received, "hi", 2) == 2);
    char rb[4];
    CHECK(read(pfd[0], rb, 4) == 2 && memcmp(rb, "hi", 2) == 0);
    close(received);
    CHECK(send(sv[0], "abc", 3, 0) == 3 && recv(sv[1], rb, 4, 0) == 3 && memcmp(rb, "abc", 3) == 0);
    CHECK(shutdown(sv[0], SHUT_WR) == 0 && recv(sv[1], rb, 4, 0) == 0);
    close(sv[0]);
    close(sv[1]);
    close(pfd[0]);
    close(pfd[1]);

    // TCP over loopback: fork a server.
    int srv = socket(AF_INET, SOCK_STREAM, 0);
    CHECK(srv >= 0);
    int one = 1;
    CHECK(setsockopt(srv, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one) == 0);
    struct sockaddr_in addr;
    memset(&addr, 0, sizeof addr);
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    addr.sin_port = 0;
    CHECK(bind(srv, (struct sockaddr *)&addr, sizeof addr) == 0);
    socklen_t alen = sizeof addr;
    CHECK(getsockname(srv, (struct sockaddr *)&addr, &alen) == 0 && addr.sin_port != 0);
    CHECK(listen(srv, 8) == 0);
    int type = 0;
    socklen_t tlen = sizeof type;
    CHECK(getsockopt(srv, SOL_SOCKET, SO_TYPE, &type, &tlen) == 0 && type == SOCK_STREAM);
    pid_t child = fork();
    CHECK(child >= 0);
    if (child == 0) {
        struct sockaddr_in peer;
        socklen_t plen = sizeof peer;
        int c = accept(srv, (struct sockaddr *)&peer, &plen);
        if (c < 0) _exit(1);
        char buf[64];
        ssize_t n = recv(c, buf, sizeof buf, 0);
        if (n <= 0) _exit(2);
        for (ssize_t i = 0; i < n; i++) buf[i] = (char)(buf[i] - 32);
        if (send(c, buf, n, 0) != n) _exit(3);
        close(c);
        _exit(0);
    }
    int cli = socket(AF_INET, SOCK_STREAM, 0);
    CHECK(cli >= 0);
    CHECK(setsockopt(cli, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one) == 0);
    CHECK(connect(cli, (struct sockaddr *)&addr, sizeof addr) == 0);
    struct sockaddr_in peer;
    socklen_t plen = sizeof peer;
    CHECK(getpeername(cli, (struct sockaddr *)&peer, &plen) == 0 && peer.sin_port == addr.sin_port);
    CHECK(send(cli, "hello", 5, 0) == 5);
    struct pollfd pfd1 = {cli, POLLIN, 0};
    CHECK(poll(&pfd1, 1, 5000) == 1 && (pfd1.revents & POLLIN));
    char resp[16];
    CHECK(recv(cli, resp, sizeof resp, 0) == 5 && memcmp(resp, "HELLO", 5) == 0);
    close(cli);
    int status;
    CHECK(waitpid(child, &status, 0) == child && WEXITSTATUS(status) == 0);
    close(srv);

    // UDP.
    int u1 = socket(AF_INET, SOCK_DGRAM, 0), u2 = socket(AF_INET, SOCK_DGRAM, 0);
    CHECK(u1 >= 0 && u2 >= 0);
    addr.sin_port = 0;
    CHECK(bind(u1, (struct sockaddr *)&addr, sizeof addr) == 0);
    alen = sizeof addr;
    CHECK(getsockname(u1, (struct sockaddr *)&addr, &alen) == 0);
    CHECK(sendto(u2, "dgram", 5, 0, (struct sockaddr *)&addr, sizeof addr) == 5);
    struct sockaddr_in from;
    socklen_t flen = sizeof from;
    CHECK(recvfrom(u1, resp, sizeof resp, 0, (struct sockaddr *)&from, &flen) == 5 && flen == sizeof from);
    CHECK(from.sin_family == AF_INET && memcmp(resp, "dgram", 5) == 0);
    close(u1);
    close(u2);

    // getaddrinfo.
    struct addrinfo hints, *res;
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_STREAM;
    CHECK(getaddrinfo("localhost", "http", &hints, &res) == 0);
    CHECK(res->ai_family == AF_INET && ((struct sockaddr_in *)res->ai_addr)->sin_port == htons(80));
    CHECK(inet_ntop(AF_INET, &((struct sockaddr_in *)res->ai_addr)->sin_addr, text, sizeof text) && strcmp(text, "127.0.0.1") == 0);
    char host[NI_MAXHOST], serv[NI_MAXSERV];
    CHECK(getnameinfo(res->ai_addr, res->ai_addrlen, host, sizeof host, serv, sizeof serv, NI_NUMERICHOST | NI_NUMERICSERV) == 0);
    CHECK(strcmp(host, "127.0.0.1") == 0 && strcmp(serv, "80") == 0);
    freeaddrinfo(res);
    hints.ai_family = AF_UNSPEC;
    hints.ai_flags = AI_PASSIVE;
    CHECK(getaddrinfo(NULL, "8080", &hints, &res) == 0 && res->ai_next != NULL);
    freeaddrinfo(res);
    int rc = getaddrinfo("no.such.host.invalid", NULL, NULL, &res);
    CHECK(rc == EAI_NONAME && strcmp(gai_strerror(rc), "Name or service not known") == 0);
    struct hostent *he = gethostbyname("localhost");
    CHECK(he && he->h_addrtype == AF_INET && he->h_length == 4 && he->h_addr_list[0][0] == 127);

    // select and epoll on a pipe, eventfd.
    CHECK(pipe(pfd) == 0);
    fd_set rs;
    FD_ZERO(&rs);
    FD_SET(pfd[0], &rs);
    struct timeval tv = {0, 10000};
    CHECK(select(pfd[0] + 1, &rs, NULL, NULL, &tv) == 0 && !FD_ISSET(pfd[0], &rs));
    CHECK(write(pfd[1], "x", 1) == 1);
    FD_SET(pfd[0], &rs);
    tv.tv_sec = 1;
    tv.tv_usec = 0;
    CHECK(select(pfd[0] + 1, &rs, NULL, NULL, &tv) == 1 && FD_ISSET(pfd[0], &rs));
    int ep = epoll_create1(EPOLL_CLOEXEC);
    CHECK(ep >= 0);
    struct epoll_event ev;
    ev.events = EPOLLIN;
    ev.data.u64 = 0x1122334455667788ull;
    CHECK(epoll_ctl(ep, EPOLL_CTL_ADD, pfd[0], &ev) == 0);
    struct epoll_event out[4];
    CHECK(epoll_wait(ep, out, 4, 1000) == 1 && (out[0].events & EPOLLIN) && out[0].data.u64 == 0x1122334455667788ull);
    CHECK(read(pfd[0], rb, 1) == 1);
    CHECK(epoll_wait(ep, out, 4, 0) == 0);
    CHECK(epoll_ctl(ep, EPOLL_CTL_DEL, pfd[0], NULL) == 0);
    close(ep);
    int efd = eventfd(3, EFD_CLOEXEC);
    CHECK(efd >= 0);
    CHECK(eventfd_write(efd, 4) == 0);
    eventfd_t val;
    CHECK(eventfd_read(efd, &val) == 0 && val == 7);
    close(efd);
    struct pollfd pp = {pfd[0], POLLIN, 0};
    struct timespec ts = {0, 5000000};
    CHECK(ppoll(&pp, 1, &ts, NULL) == 0);
    close(pfd[0]);
    close(pfd[1]);
    return 0;
}
