// File system calls: open/stat/dirs/links/perms/mmap/dirent/getcwd/realpath.
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <libgen.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/uio.h>
#include <sys/utsname.h>
#include <unistd.h>

#if defined(__x86_64__)
#define MACHINE "x86_64"
#else
#define MACHINE "aarch64"
#endif
#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

int main(void) {
    char tmpl[] = "/tmp/rustlibc-fs-XXXXXX";
    CHECK(mkdtemp(tmpl) != NULL);
    char path[512], lnk[512], cwd[512];
    snprintf(path, sizeof path, "%s/file", tmpl);
    int fd = open(path, O_WRONLY | O_CREAT | O_EXCL, 0640);
    CHECK(fd >= 0);
    CHECK(open(path, O_WRONLY | O_CREAT | O_EXCL, 0640) == -1 && errno == EEXIST);
    struct iovec iov[2] = {{"hello ", 6}, {"world\n", 6}};
    CHECK(writev(fd, iov, 2) == 12);
    CHECK(fsync(fd) == 0);
    struct stat st;
    CHECK(fstat(fd, &st) == 0 && st.st_size == 12 && S_ISREG(st.st_mode) && (st.st_mode & 0777) == 0640);
    CHECK(ftruncate(fd, 5) == 0 && fstat(fd, &st) == 0 && st.st_size == 5);
    CHECK(close(fd) == 0);
    CHECK(stat(path, &st) == 0 && st.st_size == 5);
    CHECK(chmod(path, 0600) == 0 && stat(path, &st) == 0 && (st.st_mode & 0777) == 0600);
    CHECK(access(path, R_OK | W_OK) == 0 && access(path, X_OK) == -1 && errno == EACCES);

    snprintf(lnk, sizeof lnk, "%s/link", tmpl);
    CHECK(symlink("file", lnk) == 0);
    CHECK(lstat(lnk, &st) == 0 && S_ISLNK(st.st_mode));
    CHECK(stat(lnk, &st) == 0 && S_ISREG(st.st_mode));
    char target[64];
    ssize_t n = readlink(lnk, target, sizeof target);
    CHECK(n == 4 && memcmp(target, "file", 4) == 0);
    char hard[512];
    snprintf(hard, sizeof hard, "%s/hard", tmpl);
    CHECK(link(path, hard) == 0 && stat(hard, &st) == 0 && st.st_nlink == 2);
    char renamed[512];
    snprintf(renamed, sizeof renamed, "%s/renamed", tmpl);
    CHECK(rename(hard, renamed) == 0 && access(hard, F_OK) == -1 && access(renamed, F_OK) == 0);

    // Directories.
    char sub[512];
    snprintf(sub, sizeof sub, "%s/sub", tmpl);
    CHECK(mkdir(sub, 0755) == 0 && mkdir(sub, 0755) == -1 && errno == EEXIST);
    CHECK(getcwd(cwd, sizeof cwd) != NULL && cwd[0] == '/');
    CHECK(chdir(tmpl) == 0);
    char here[512];
    CHECK(getcwd(here, sizeof here) != NULL);
    char *resolved = realpath(tmpl, NULL);
    CHECK(resolved && strcmp(resolved, here) == 0);
    free(resolved);
    char *dyn = getcwd(NULL, 0);
    CHECK(dyn && strcmp(dyn, here) == 0);
    free(dyn);
    CHECK(chdir(cwd) == 0);

    DIR *d = opendir(tmpl);
    CHECK(d != NULL);
    int seen_file = 0, seen_sub = 0, seen_link = 0, count = 0;
    struct dirent *e;
    while ((e = readdir(d)) != NULL) {
        count++;
        if (strcmp(e->d_name, "file") == 0) { seen_file = 1; CHECK(e->d_type == DT_REG); }
        if (strcmp(e->d_name, "sub") == 0) { seen_sub = 1; CHECK(e->d_type == DT_DIR); }
        if (strcmp(e->d_name, "link") == 0) { seen_link = 1; CHECK(e->d_type == DT_LNK); }
    }
    CHECK(seen_file && seen_sub && seen_link && count == 6);  // . .. file link renamed sub
    rewinddir(d);
    CHECK(readdir(d) != NULL);
    CHECK(closedir(d) == 0);
    struct dirent **list;
    int nlist = scandir(tmpl, &list, NULL, alphasort);
    CHECK(nlist == 6);
    CHECK(strcmp(list[0]->d_name, ".") == 0 && strcmp(list[2]->d_name, "file") == 0 && strcmp(list[5]->d_name, "sub") == 0);
    for (int i = 0; i < nlist; i++) free(list[i]);
    free(list);
    CHECK(opendir(path) == NULL && errno == ENOTDIR);

    // mmap a file.
    fd = open(path, O_RDWR);
    CHECK(fd >= 0);
    char *map = mmap(NULL, 4096, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    CHECK(map != MAP_FAILED);
    CHECK(memcmp(map, "hello", 5) == 0);
    map[0] = 'j';
    CHECK(msync(map, 4096, MS_SYNC) == 0);
    CHECK(munmap(map, 4096) == 0);
    char rb[8];
    CHECK(pread(fd, rb, 5, 0) == 5 && memcmp(rb, "jello", 5) == 0);
    CHECK(pwrite(fd, "J", 1, 0) == 1 && lseek(fd, 0, SEEK_END) == 5);
    CHECK(fcntl(fd, F_GETFL) >= 0 && (fcntl(fd, F_GETFL) & O_ACCMODE) == O_RDWR);
    CHECK(fcntl(fd, F_SETFD, FD_CLOEXEC) == 0 && fcntl(fd, F_GETFD) == FD_CLOEXEC);
    int dupfd = dup(fd);
    CHECK(dupfd > fd && close(dupfd) == 0);
    CHECK(close(fd) == 0);
    CHECK(mmap(NULL, 0, PROT_READ, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0) == MAP_FAILED && errno == EINVAL);
    void *anon = mmap(NULL, 1 << 20, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    CHECK(anon != MAP_FAILED);
    memset(anon, 1, 1 << 20);
    CHECK(mprotect(anon, 4096, PROT_READ) == 0 && madvise(anon, 4096, MADV_DONTNEED) == 0);
    CHECK(munmap(anon, 1 << 20) == 0);

    // Cleanup.
    CHECK(unlink(path) == 0 && unlink(lnk) == 0 && unlink(renamed) == 0 && rmdir(sub) == 0 && rmdir(tmpl) == 0);
    CHECK(unlink(path) == -1 && errno == ENOENT);

    // System information.
    struct utsname u;
    CHECK(uname(&u) == 0 && strcmp(u.sysname, "Linux") == 0 && strcmp(u.machine, MACHINE) == 0);
    char host[256];
    CHECK(gethostname(host, sizeof host) == 0 && strcmp(host, u.nodename) == 0);
    CHECK(sysconf(_SC_PAGESIZE) == 4096 && getpagesize() == 4096);
    CHECK(sysconf(_SC_NPROCESSORS_ONLN) >= 1 && sysconf(_SC_OPEN_MAX) >= 256);
    struct rlimit rl;
    CHECK(getrlimit(RLIMIT_NOFILE, &rl) == 0 && rl.rlim_cur >= 256 && rl.rlim_cur <= rl.rlim_max);
    CHECK(getuid() == geteuid() && getpid() > 0 && getppid() > 0);
    mode_t old = umask(022);
    CHECK(umask(old) == 022);
    char p1[] = "/a/b/c", p2[] = "/a/b/c";
    CHECK(strcmp(basename(p1), "c") == 0 && strcmp(dirname(p2), "/a/b") == 0);
    CHECK(isatty(0) == 0 && errno == ENOTTY);
    CHECK(ttyname(0) == NULL);
    return 0;
}
