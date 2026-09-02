// The DNS resolver against a fake nameserver run in a child process:
// A/AAAA answers, CNAME chains, truncation with TCP fallback, NXDOMAIN,
// the search list, PTR lookups, and timeouts.
#include <arpa/inet.h>
#include <errno.h>
#include <netdb.h>
#include <netinet/in.h>
#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

void __rustlibc_set_resolv_conf(const char *);

// --- a tiny DNS server ---------------------------------------------------

static size_t put_name(unsigned char *p, const char *name) {
    size_t n = 0;
    while (*name) {
        const char *dot = strchr(name, '.');
        size_t l = dot ? (size_t)(dot - name) : strlen(name);
        p[n++] = (unsigned char)l;
        memcpy(p + n, name, l);
        n += l;
        name += l;
        if (*name == '.') name++;
    }
    p[n++] = 0;
    return n;
}

static size_t put_rr(unsigned char *p, const char *owner, int type, const unsigned char *data, size_t dlen) {
    size_t n = put_name(p, owner);
    p[n++] = type >> 8; p[n++] = type & 0xff;
    p[n++] = 0; p[n++] = 1;
    p[n++] = 0; p[n++] = 0; p[n++] = 0; p[n++] = 60;
    p[n++] = dlen >> 8; p[n++] = dlen & 0xff;
    memcpy(p + n, data, dlen);
    return n + dlen;
}

// Decodes the (uncompressed) question name into `out`; returns the qtype.
static int parse_question(const unsigned char *q, size_t len, char *out, size_t *qend) {
    size_t pos = 12, n = 0;
    while (pos < len && q[pos]) {
        size_t l = q[pos++];
        if (pos + l > len) return -1;
        if (n) out[n++] = '.';
        memcpy(out + n, q + pos, l);
        n += l;
        pos += l;
    }
    out[n] = 0;
    pos++;
    *qend = pos + 4;
    return (q[pos] << 8) | q[pos + 1];
}

// Builds the reply for `query` in `r`; returns its length.
static size_t answer(const unsigned char *q, size_t qlen, unsigned char *r, int over_tcp) {
    char name[256];
    size_t qend = 12;
    int qtype = parse_question(q, qlen, name, &qend);
    if (qtype < 0) return 0;
    memcpy(r, q, qend);
    r[2] = 0x81; r[3] = 0x80; // QR, RD, RA, NOERROR
    r[6] = r[7] = 0;
    size_t n = qend;
    int ancount = 0;
    const unsigned char a1[4] = {10, 1, 2, 3}, a2[4] = {10, 9, 9, 9}, a3[4] = {10, 5, 5, 5};
    const unsigned char aaaa[16] = {0x20, 0x01, 0x0d, 0xb8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1};
    unsigned char target[64];
    if (strcmp(name, "www.test") == 0) {
        if (qtype == 1) { n += put_rr(r + n, "www.test", 1, a1, 4); ancount++; }
        if (qtype == 28) { n += put_rr(r + n, "www.test", 28, aaaa, 16); ancount++; }
    } else if (strcmp(name, "alias.test") == 0) {
        size_t tl = put_name(target, "www.test");
        n += put_rr(r + n, "alias.test", 5, target, tl); ancount++;
        // A decoy record for another name must be ignored.
        n += put_rr(r + n, "other.test", 1, a2, 4); ancount++;
        if (qtype == 1) { n += put_rr(r + n, "www.test", 1, a1, 4); ancount++; }
    } else if (strcmp(name, "big.test") == 0) {
        if (!over_tcp) {
            r[2] |= 0x02; // truncated, no answers
        } else if (qtype == 1) {
            n += put_rr(r + n, "big.test", 1, a2, 4); ancount++;
        }
    } else if (strcmp(name, "host.test") == 0) {
        if (qtype == 1) { n += put_rr(r + n, "host.test", 1, a3, 4); ancount++; }
    } else if (strcmp(name, "3.2.1.10.in-addr.arpa") == 0 && qtype == 12) {
        size_t tl = put_name(target, "www.test");
        n += put_rr(r + n, "3.2.1.10.in-addr.arpa", 12, target, tl); ancount++;
    } else {
        r[3] = 0x83; // NXDOMAIN
    }
    r[6] = ancount >> 8; r[7] = ancount & 0xff;
    return n;
}

static void serve(int udp, int tcp) {
    struct pollfd fds[2] = {{udp, POLLIN, 0}, {tcp, POLLIN, 0}};
    unsigned char q[1024], r[1024];
    for (;;) {
        if (poll(fds, 2, -1) < 0) continue;
        if (fds[0].revents) {
            struct sockaddr_in from;
            socklen_t fl = sizeof from;
            ssize_t n = recvfrom(udp, q, sizeof q, 0, (struct sockaddr *)&from, &fl);
            if (n > 12) {
                size_t rl = answer(q, (size_t)n, r, 0);
                sendto(udp, r, rl, 0, (struct sockaddr *)&from, fl);
            }
        }
        if (fds[1].revents) {
            int c = accept(tcp, NULL, NULL);
            if (c < 0) continue;
            unsigned char lenbuf[2];
            if (read(c, lenbuf, 2) == 2) {
                size_t ql = (lenbuf[0] << 8) | lenbuf[1];
                size_t got = 0;
                while (got < ql) {
                    ssize_t k = read(c, q + got, ql - got);
                    if (k <= 0) break;
                    got += (size_t)k;
                }
                if (got == ql) {
                    size_t rl = answer(q, ql, r + 2, 1);
                    r[0] = rl >> 8; r[1] = rl & 0xff;
                    write(c, r, rl + 2);
                }
            }
            close(c);
        }
    }
}

// --- the test --------------------------------------------------------------

static int has_v4(struct addrinfo *res, const char *ip) {
    for (struct addrinfo *p = res; p; p = p->ai_next) {
        char buf[64];
        if (p->ai_family == AF_INET && p->ai_socktype == SOCK_STREAM) {
            inet_ntop(AF_INET, &((struct sockaddr_in *)p->ai_addr)->sin_addr, buf, sizeof buf);
            if (strcmp(buf, ip) == 0) return 1;
        }
    }
    return 0;
}

static int has_v6(struct addrinfo *res, const char *ip) {
    for (struct addrinfo *p = res; p; p = p->ai_next) {
        char buf[64];
        if (p->ai_family == AF_INET6 && p->ai_socktype == SOCK_STREAM) {
            inet_ntop(AF_INET6, &((struct sockaddr_in6 *)p->ai_addr)->sin6_addr, buf, sizeof buf);
            if (strcmp(buf, ip) == 0) return 1;
        }
    }
    return 0;
}

int main(void) {
    int udp = socket(AF_INET, SOCK_DGRAM, 0), tcp = socket(AF_INET, SOCK_STREAM, 0);
    CHECK(udp >= 0 && tcp >= 0);
    struct sockaddr_in sa = {.sin_family = AF_INET, .sin_port = 0, .sin_addr = {htonl(0x7f000001)}};
    CHECK(bind(udp, (struct sockaddr *)&sa, sizeof sa) == 0);
    socklen_t sl = sizeof sa;
    CHECK(getsockname(udp, (struct sockaddr *)&sa, &sl) == 0);
    int port = ntohs(sa.sin_port);
    int one = 1;
    setsockopt(tcp, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    CHECK(bind(tcp, (struct sockaddr *)&sa, sizeof sa) == 0 && listen(tcp, 8) == 0);
    pid_t server = fork();
    CHECK(server >= 0);
    if (server == 0) {
        // Die with the parent and release its output pipes.
        prctl(PR_SET_PDEATHSIG, SIGKILL);
        close(0);
        close(1);
        close(2);
        serve(udp, tcp);
        _exit(0);
    }
    close(udp);
    close(tcp);

    char dir[] = "/tmp/rustlibc-dns-XXXXXX";
    CHECK(mkdtemp(dir));
    static char conf[300];
    snprintf(conf, sizeof conf, "%s/resolv.conf", dir);
    FILE *f = fopen(conf, "w");
    CHECK(f);
    fprintf(f, "nameserver 127.0.0.1:%d\nsearch test\noptions timeout:2 attempts:2\n", port);
    fclose(f);
    __rustlibc_set_resolv_conf(conf);

    struct addrinfo hints = {0}, *res = NULL;
    hints.ai_socktype = SOCK_STREAM;
    CHECK(getaddrinfo("www.test", "80", &hints, &res) == 0);
    CHECK(has_v4(res, "10.1.2.3") && has_v6(res, "2001:db8::1"));
    CHECK(ntohs(((struct sockaddr_in *)res->ai_addr)->sin_port) == 80);
    freeaddrinfo(res);

    hints.ai_family = AF_INET;
    hints.ai_flags = AI_CANONNAME;
    CHECK(getaddrinfo("alias.test", NULL, &hints, &res) == 0);
    CHECK(has_v4(res, "10.1.2.3") && !has_v4(res, "10.9.9.9"));
    CHECK(res->ai_canonname && strcmp(res->ai_canonname, "www.test") == 0);
    freeaddrinfo(res);

    CHECK(getaddrinfo("big.test", NULL, &hints, &res) == 0);
    CHECK(has_v4(res, "10.9.9.9"));
    freeaddrinfo(res);

    CHECK(getaddrinfo("nx.test", NULL, &hints, &res) == EAI_NONAME);
    CHECK(getaddrinfo("host", NULL, &hints, &res) == 0); // via the search list
    CHECK(has_v4(res, "10.5.5.5"));
    freeaddrinfo(res);
    CHECK(getaddrinfo("bad name", NULL, &hints, &res) == EAI_NONAME);

    struct sockaddr_in q = {.sin_family = AF_INET, .sin_port = htons(22)};
    inet_pton(AF_INET, "10.1.2.3", &q.sin_addr);
    char host[NI_MAXHOST], serv[NI_MAXSERV];
    CHECK(getnameinfo((struct sockaddr *)&q, sizeof q, host, sizeof host, serv, sizeof serv, 0) == 0);
    CHECK(strcmp(host, "www.test") == 0 && strcmp(serv, "22") == 0);
    CHECK(getnameinfo((struct sockaddr *)&q, sizeof q, host, sizeof host, NULL, 0, NI_NOFQDN) == 0);
    CHECK(strcmp(host, "www") == 0);
    CHECK(getnameinfo((struct sockaddr *)&q, sizeof q, host, sizeof host, NULL, 0, NI_NUMERICHOST) == 0);
    CHECK(strcmp(host, "10.1.2.3") == 0);
    inet_pton(AF_INET, "10.7.7.7", &q.sin_addr);
    CHECK(getnameinfo((struct sockaddr *)&q, sizeof q, host, sizeof host, NULL, 0, NI_NAMEREQD) == EAI_NONAME);
    CHECK(getnameinfo((struct sockaddr *)&q, sizeof q, host, sizeof host, NULL, 0, 0) == 0 && strcmp(host, "10.7.7.7") == 0);

    struct hostent *he = gethostbyname("alias.test");
    CHECK(he && strcmp(he->h_name, "www.test") == 0 && he->h_length == 4);
    CHECK(memcmp(he->h_addr_list[0], "\x0a\x01\x02\x03", 4) == 0 && he->h_addr_list[1] == NULL);
    CHECK(gethostbyname("nx.test") == NULL && h_errno == HOST_NOT_FOUND);
    he = gethostbyname2("www.test", AF_INET6);
    CHECK(he && he->h_length == 16 && he->h_addrtype == AF_INET6);
    unsigned char raw[4] = {10, 1, 2, 3};
    he = gethostbyaddr(raw, 4, AF_INET);
    CHECK(he && strcmp(he->h_name, "www.test") == 0);

    // An unreachable server: EAI_AGAIN after the (short) timeout.
    f = fopen(conf, "w");
    fprintf(f, "nameserver 127.0.0.1:%d\noptions timeout:1 attempts:1\n", port == 1 ? 2 : 1);
    fclose(f);
    CHECK(getaddrinfo("www.test", NULL, &hints, &res) == EAI_AGAIN);

    kill(server, SIGKILL);
    waitpid(server, NULL, 0);
    unlink(conf);
    rmdir(dir);
    return 0;
}
