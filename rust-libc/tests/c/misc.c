// Batch of smaller interfaces: fnmatch, search.h, *rand48, popen, ptys,
// termios, timerfd/inotify/signalfd, lockf, sbrk, getsubopt, statfs,
// sched, syslog, utime, quick_exit.
// expect-exit: 7
#include <errno.h>
#include <fcntl.h>
#include <fnmatch.h>
#include <sched.h>
#include <search.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/inotify.h>
#include <sys/mman.h>
#include <sys/signalfd.h>
#include <sys/stat.h>
#include <sys/statfs.h>
#include <sys/timerfd.h>
#include <sys/wait.h>
#include <syslog.h>
#include <termios.h>
#include <unistd.h>
#include <utime.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

static int cmp_int(const void *a, const void *b) {
    int x = *(const int *)a, y = *(const int *)b;
    return (x > y) - (x < y);
}

static int walk_sum, walk_leaves;
static void walker(const void *node, VISIT v, int depth) {
    (void)depth;
    if (v == postorder || v == leaf) walk_sum += **(const int *const *)node;
    if (v == leaf) walk_leaves++;
}

static void on_quick(void) { write(1, "quick\n", 6); }

static int test_fnmatch(void) {
    CHECK(fnmatch("*.c", "misc.c", 0) == 0);
    CHECK(fnmatch("*.c", "misc.h", 0) == FNM_NOMATCH);
    CHECK(fnmatch("a?c", "abc", 0) == 0);
    CHECK(fnmatch("[a-c]x", "bx", 0) == 0);
    CHECK(fnmatch("[!a-c]x", "bx", 0) == FNM_NOMATCH);
    CHECK(fnmatch("[[:digit:]]*", "7up", 0) == 0);
    CHECK(fnmatch("*", "dir/file", FNM_PATHNAME) == FNM_NOMATCH);
    CHECK(fnmatch("*/*", "dir/file", FNM_PATHNAME) == 0);
    CHECK(fnmatch("*", ".hidden", FNM_PERIOD) == FNM_NOMATCH);
    CHECK(fnmatch(".*", ".hidden", FNM_PERIOD) == 0);
    CHECK(fnmatch("ABC", "abc", FNM_CASEFOLD) == 0);
    CHECK(fnmatch("\\*", "*", 0) == 0);
    CHECK(fnmatch("\\*", "x", 0) == FNM_NOMATCH);
    CHECK(fnmatch("\\*", "\\*", FNM_NOESCAPE) == 0);
    CHECK(fnmatch("dir", "dir/sub/file", FNM_LEADING_DIR) == 0);
    CHECK(fnmatch("a*b*c", "axxbyyc", 0) == 0);
    CHECK(fnmatch("a*b*c", "axxbyy", 0) == FNM_NOMATCH);
    return 0;
}

static int test_search(void) {
    void *root = NULL;
    static int keys[] = {5, 3, 8, 1, 4, 7, 9};
    for (size_t i = 0; i < sizeof keys / sizeof *keys; i++) {
        int **r = tsearch(&keys[i], &root, cmp_int);
        CHECK(r && *r == &keys[i]);
    }
    int five = 5;
    CHECK(*(int **)tsearch(&five, &root, cmp_int) == &keys[0]); // existing
    int six = 6;
    CHECK(tfind(&six, &root, cmp_int) == NULL);
    CHECK(*(int **)tfind(&five, &root, cmp_int) == &keys[0]);
    walk_sum = 0;
    twalk(root, walker);
    CHECK(walk_sum == 37 && walk_leaves >= 1);
    CHECK(tdelete(&five, &root, cmp_int) != NULL);
    CHECK(tfind(&five, &root, cmp_int) == NULL);
    CHECK(tdelete(&five, &root, cmp_int) == NULL);
    walk_sum = 0;
    twalk(root, walker);
    CHECK(walk_sum == 32);
    tdestroy(root, NULL);

    CHECK(hcreate(4) != 0);
    ENTRY e = {"alpha", (void *)1}, *ep;
    CHECK(hsearch(e, ENTER) != NULL);
    e.key = "beta"; e.data = (void *)2;
    CHECK(hsearch(e, ENTER) != NULL);
    e.key = "gamma"; e.data = (void *)3;
    CHECK(hsearch(e, ENTER) != NULL);
    e.key = "beta"; e.data = (void *)99;
    ep = hsearch(e, FIND);
    CHECK(ep && ep->data == (void *)2 && strcmp(ep->key, "beta") == 0);
    e.key = "delta";
    CHECK(hsearch(e, FIND) == NULL && errno == ESRCH);
    hdestroy();

    struct hsearch_data tab;
    memset(&tab, 0, sizeof tab);
    CHECK(hcreate_r(100, &tab) != 0);
    char names[50][8];
    for (int i = 0; i < 50; i++) {
        snprintf(names[i], sizeof names[i], "k%d", i);
        ENTRY item = {names[i], (void *)(long)(i + 1)};
        CHECK(hsearch_r(item, ENTER, &ep, &tab) != 0);
    }
    for (int i = 0; i < 50; i++) {
        ENTRY item = {names[i], NULL};
        CHECK(hsearch_r(item, FIND, &ep, &tab) != 0 && ep->data == (void *)(long)(i + 1));
    }
    hdestroy_r(&tab);

    int arr[8] = {3, 1, 2};
    size_t n = 3;
    int two = 2, nine = 9;
    CHECK(lfind(&two, arr, &n, sizeof(int), cmp_int) == &arr[2]);
    CHECK(lfind(&nine, arr, &n, sizeof(int), cmp_int) == NULL);
    CHECK(lsearch(&nine, arr, &n, sizeof(int), cmp_int) == &arr[3] && n == 4 && arr[3] == 9);
    CHECK(lsearch(&two, arr, &n, sizeof(int), cmp_int) == &arr[2] && n == 4);

    struct q { struct q *fwd, *back; int v; } a = {0}, b = {0}, c = {0};
    a.v = 1; b.v = 2; c.v = 3;
    insque(&a, NULL);
    insque(&b, &a);
    insque(&c, &a);
    CHECK(a.fwd == &c && c.fwd == &b && b.back == &c && c.back == &a && a.back == NULL && b.fwd == NULL);
    remque(&c);
    CHECK(a.fwd == &b && b.back == &a);
    return 0;
}

static int test_rand48(void) {
    srand48(12345);
    double d1 = drand48(), d2 = drand48();
    long l1 = lrand48();
    long m1 = mrand48();
    CHECK(d1 >= 0 && d1 < 1 && d2 >= 0 && d2 < 1 && d1 != d2);
    CHECK(l1 >= 0 && l1 < (1L << 31));
    CHECK(m1 >= -(1L << 31) && m1 < (1L << 31));
    srand48(12345);
    CHECK(drand48() == d1 && drand48() == d2 && lrand48() == l1 && mrand48() == m1);
    // srand48(s) is x = (s << 16) | 0x330E, so erand48 with that state matches.
    unsigned short x[3] = {0x330E, 12345 & 0xffff, 12345 >> 16};
    CHECK(erand48(x) == d1 && erand48(x) == d2 && nrand48(x) == l1 && jrand48(x) == m1);
    unsigned short seed[3] = {1, 2, 3};
    unsigned short *old = seed48(seed);
    CHECK(old != NULL);
    unsigned short saved[3] = {old[0], old[1], old[2]};
    (void)saved;
    double s1 = drand48();
    unsigned short again[3] = {1, 2, 3};
    seed48(again);
    CHECK(drand48() == s1);
    return 0;
}

static int test_popen(char *dir) {
    FILE *f = popen("echo hello from sh; exit 3", "r");
    CHECK(f != NULL);
    char line[64];
    CHECK(fgets(line, sizeof line, f) != NULL && strcmp(line, "hello from sh\n") == 0);
    int st = pclose(f);
    CHECK(WIFEXITED(st) && WEXITSTATUS(st) == 3);

    char cmd[600];
    snprintf(cmd, sizeof cmd, "cat > %s/popen.out", dir);
    f = popen(cmd, "w");
    CHECK(f != NULL);
    CHECK(fputs("written via popen\n", f) >= 0);
    CHECK(pclose(f) == 0);
    snprintf(cmd, sizeof cmd, "%s/popen.out", dir);
    f = fopen(cmd, "r");
    CHECK(f && fgets(line, sizeof line, f) && strcmp(line, "written via popen\n") == 0);
    fclose(f);
    CHECK(popen("true", "x") == NULL && errno == EINVAL);
    return 0;
}

static int test_pty(void) {
    int m = posix_openpt(O_RDWR | O_NOCTTY);
    if (m < 0 && (errno == ENOENT || errno == EACCES)) return 0; // no devpts here
    CHECK(m >= 0);
    CHECK(grantpt(m) == 0 && unlockpt(m) == 0);
    char name[64];
    CHECK(ptsname_r(m, name, sizeof name) == 0 && strncmp(name, "/dev/pts/", 9) == 0);
    CHECK(strcmp(ptsname(m), name) == 0);
    CHECK(ptsname_r(m, name, 4) == ERANGE);
    int s = open(name, O_RDWR | O_NOCTTY);
    CHECK(s >= 0);
    struct termios t;
    CHECK(tcgetattr(s, &t) == 0);
    CHECK(t.c_lflag & ICANON);
    cfmakeraw(&t);
    CHECK(!(t.c_lflag & (ICANON | ECHO)) && t.c_cc[VMIN] == 1);
    CHECK(cfsetispeed(&t, B9600) == 0 && cfgetispeed(&t) == B9600);
    CHECK(cfsetospeed(&t, B38400) == 0 && cfgetospeed(&t) == B38400);
    CHECK(cfsetispeed(&t, B0) == 0 && cfgetispeed(&t) == B38400); // B0 = "same as output"
    CHECK(tcsetattr(s, TCSANOW, &t) == 0);
    struct termios u;
    CHECK(tcgetattr(s, &u) == 0 && !(u.c_lflag & ICANON) && cfgetospeed(&u) == B38400);
    CHECK(write(m, "abc", 3) == 3);
    char buf[8];
    CHECK(read(s, buf, 3) == 3 && memcmp(buf, "abc", 3) == 0);
    CHECK(tcflush(s, TCIOFLUSH) == 0 && tcdrain(s) == 0);
    CHECK(tcgetattr(0, &t) == -1 && errno == ENOTTY); // stdin is not a tty in tests
    close(s);
    close(m);
    return 0;
}

static int test_fds(char *dir) {
    int tfd = timerfd_create(CLOCK_MONOTONIC, TFD_CLOEXEC);
    CHECK(tfd >= 0);
    struct itimerspec its = {{0, 0}, {0, 5 * 1000 * 1000}};
    CHECK(timerfd_settime(tfd, 0, &its, NULL) == 0);
    unsigned long long ticks = 0;
    CHECK(read(tfd, &ticks, sizeof ticks) == sizeof ticks && ticks == 1);
    struct itimerspec cur;
    CHECK(timerfd_gettime(tfd, &cur) == 0 && cur.it_value.tv_sec == 0 && cur.it_value.tv_nsec == 0);
    close(tfd);

    int ifd = inotify_init1(IN_CLOEXEC);
    CHECK(ifd >= 0);
    int wd = inotify_add_watch(ifd, dir, IN_CREATE);
    CHECK(wd >= 0);
    char path[600];
    snprintf(path, sizeof path, "%s/watched", dir);
    close(open(path, O_WRONLY | O_CREAT, 0600));
    char ebuf[sizeof(struct inotify_event) + 256];
    ssize_t n = read(ifd, ebuf, sizeof ebuf);
    struct inotify_event *ev = (struct inotify_event *)ebuf;
    CHECK(n >= (ssize_t)sizeof *ev && ev->wd == wd && (ev->mask & IN_CREATE) && strcmp(ev->name, "watched") == 0);
    CHECK(inotify_rm_watch(ifd, wd) == 0);
    close(ifd);

    sigset_t set;
    sigemptyset(&set);
    sigaddset(&set, SIGUSR1);
    CHECK(sigprocmask(SIG_BLOCK, &set, NULL) == 0);
    int sfd = signalfd(-1, &set, SFD_CLOEXEC);
    CHECK(sfd >= 0);
    raise(SIGUSR1);
    struct signalfd_siginfo si;
    CHECK(read(sfd, &si, sizeof si) == sizeof si && si.ssi_signo == SIGUSR1 && si.ssi_pid == (unsigned)getpid());
    close(sfd);
    CHECK(sigprocmask(SIG_UNBLOCK, &set, NULL) == 0);
    return 0;
}

static int test_unistd(char *dir) {
    char path[600];
    snprintf(path, sizeof path, "%s/lock", dir);
    int fd = open(path, O_RDWR | O_CREAT, 0600);
    CHECK(fd >= 0);
    CHECK(lockf(fd, F_LOCK, 0) == 0);
    CHECK(lockf(fd, F_TEST, 0) == 0); // our own lock
    CHECK(lockf(fd, F_ULOCK, 0) == 0);
    CHECK(lockf(fd, F_TLOCK, 0) == 0);
    pid_t pid = fork();
    CHECK(pid >= 0);
    if (pid == 0) {
        int fd2 = open(path, O_RDWR);
        _exit(lockf(fd2, F_TEST, 0) == -1 && (errno == EACCES || errno == EAGAIN) ? 0 : 1);
    }
    int st;
    CHECK(waitpid(pid, &st, 0) == pid && WIFEXITED(st) && WEXITSTATUS(st) == 0);

    struct utimbuf ub = {1000000000, 1234567890};
    CHECK(utime(path, &ub) == 0);
    struct stat sb;
    CHECK(stat(path, &sb) == 0 && sb.st_mtime == 1234567890 && sb.st_atime == 1000000000);
    close(fd);

    void *cur = sbrk(0);
    CHECK(cur != (void *)-1 && cur != NULL);
    char *p = sbrk(8192);
    CHECK(p != (char *)-1);
    memset(p, 0x5a, 8192);
    CHECK(p[8191] == 0x5a && (char *)sbrk(0) == p + 8192);
    CHECK(brk(p) == 0 && sbrk(0) == p);

    char opts[] = "ro,size=10,verbose";
    char *tokens[] = {"ro", "size", "verbose", NULL};
    char *sub = opts, *val;
    CHECK(getsubopt(&sub, tokens, &val) == 0 && val == NULL);
    CHECK(getsubopt(&sub, tokens, &val) == 1 && strcmp(val, "10") == 0);
    CHECK(getsubopt(&sub, tokens, &val) == 2 && *sub == '\0');

    CHECK(pathconf("/", _PC_PATH_MAX) == 4096 && fpathconf(0, _PC_NAME_MAX) == 255);
    char cs[32];
    CHECK(confstr(_CS_PATH, cs, sizeof cs) == strlen("/bin:/usr/bin") + 1 && strcmp(cs, "/bin:/usr/bin") == 0);
    CHECK(getdtablesize() >= 1024);
    unsigned char in[4] = {1, 2, 3, 4}, out[4];
    swab(in, out, 4);
    CHECK(out[0] == 2 && out[1] == 1 && out[2] == 4 && out[3] == 3);
    gid_t groups[64];
    CHECK(getgroups(64, groups) >= 0);
    uid_t r, e, s;
    CHECK(getresuid(&r, &e, &s) == 0 && r == getuid() && e == geteuid());
    double load[3];
    CHECK(getloadavg(load, 3) == 3 && load[0] >= 0);
    CHECK(secure_getenv("TESTVAR") != NULL && strcmp(secure_getenv("TESTVAR"), "value") == 0);
    CHECK(strcmp(getprogname(), "misc") == 0);

    struct statfs fs;
    CHECK(statfs("/", &fs) == 0 && fs.f_bsize > 0);
    CHECK(fstatfs(0, &fs) == 0 || errno == ENOSYS);

    CHECK(sched_getcpu() >= 0);
    cpu_set_t cpus;
    CHECK(sched_getaffinity(0, sizeof cpus, &cpus) == 0 && CPU_COUNT(&cpus) >= 1);
    CHECK(CPU_ISSET(sched_getcpu(), &cpus));
    CHECK(sched_get_priority_max(SCHED_FIFO) == 99 && sched_get_priority_min(SCHED_OTHER) == 0);
    CHECK(sched_getscheduler(0) == SCHED_OTHER);
    struct sched_param sp = {123};
    CHECK(sched_getparam(0, &sp) == 0 && sp.sched_priority == 0);

    int shm = shm_open("/rustlibc-test", O_RDWR | O_CREAT | O_EXCL, 0600);
    if (shm >= 0) {
        CHECK(ftruncate(shm, 4096) == 0);
        int *m = mmap(NULL, 4096, PROT_READ | PROT_WRITE, MAP_SHARED, shm, 0);
        CHECK(m != MAP_FAILED);
        *m = 42;
        munmap(m, 4096);
        close(shm);
        CHECK(shm_unlink("/rustlibc-test") == 0);
    } else {
        CHECK(errno == ENOENT || errno == EACCES);
    }
    CHECK(shm_open("bad/name", O_RDONLY, 0) == -1 && errno == EINVAL);

    openlog("misc", LOG_PID | LOG_NDELAY, LOG_USER);
    CHECK(setlogmask(LOG_UPTO(LOG_INFO)) == 0xff);
    syslog(LOG_INFO, "test message %d", 1); // /dev/log may not exist; must not crash
    syslog(LOG_DEBUG, "masked out");
    closelog();
    return 0;
}

int main(void) {
    char dir[] = "/tmp/rustlibc-misc-XXXXXX";
    CHECK(mkdtemp(dir) != NULL);
    int r;
    if ((r = test_fnmatch())) return r;
    if ((r = test_search())) return r;
    if ((r = test_rand48())) return r;
    if ((r = test_popen(dir))) return r;
    if ((r = test_pty())) return r;
    if ((r = test_fds(dir))) return r;
    if ((r = test_unistd(dir))) return r;
    char cmd[600];
    snprintf(cmd, sizeof cmd, "rm -rf %s", dir);
    CHECK(system(cmd) == 0);
    CHECK(at_quick_exit(on_quick) == 0);
    printf("this line is never flushed by quick_exit");
    quick_exit(7);
}
