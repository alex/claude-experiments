// ABI layout checks: every structure the kernel or the wider Linux ABI
// defines must have the size and field offsets glibc/musl use on x86_64,
// so that code written against those headers works unchanged.  Library-
// private types (pthread_*, FILE, mbstate_t) only need to agree with the
// Rust side, which asserts the same numbers.
#include <dirent.h>
#include <fcntl.h>
#include <link.h>
#include <locale.h>
#include <netdb.h>
#include <netinet/in.h>
#include <poll.h>
#include <pthread.h>
#include <pwd.h>
#include <grp.h>
#include <sched.h>
#include <search.h>
#include <semaphore.h>
#include <setjmp.h>
#include <signal.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/epoll.h>
#include <sys/inotify.h>
#include <sys/resource.h>
#include <sys/select.h>
#include <sys/signalfd.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/statfs.h>
#include <sys/sysinfo.h>
#include <sys/time.h>
#include <sys/times.h>
#include <sys/uio.h>
#include <sys/un.h>
#include <sys/utsname.h>
#include <sys/wait.h>
#include <termios.h>
#include <threads.h>
#include <time.h>
#include <wchar.h>

#define SIZE(t, n) _Static_assert(sizeof(t) == (n), "sizeof " #t " != " #n)
#define OFF(t, f, n) _Static_assert(offsetof(t, f) == (n), "offsetof " #t "." #f " != " #n)

// Kernel ABI.
#if defined(__x86_64__)
SIZE(struct stat, 144);
OFF(struct stat, st_size, 48);
OFF(struct stat, st_mtim, 88);
#else
SIZE(struct stat, 128);
OFF(struct stat, st_size, 48);
OFF(struct stat, st_mtim, 88);
#endif
SIZE(sigset_t, 128);
SIZE(struct sigaction, 152);
OFF(struct sigaction, sa_mask, 8);
OFF(struct sigaction, sa_flags, 136);
OFF(struct sigaction, sa_restorer, 144);
SIZE(siginfo_t, 128);
OFF(siginfo_t, si_pid, 16);
OFF(siginfo_t, si_addr, 16);
OFF(siginfo_t, si_status, 24);
OFF(siginfo_t, si_value, 24);
SIZE(stack_t, 24);
SIZE(struct dirent, 280);
OFF(struct dirent, d_type, 18);
OFF(struct dirent, d_name, 19);
#if defined(__x86_64__)
SIZE(struct epoll_event, 12);
OFF(struct epoll_event, data, 4);
#else
SIZE(struct epoll_event, 16);
OFF(struct epoll_event, data, 8);
#endif
SIZE(struct timespec, 16);
SIZE(struct timeval, 16);
SIZE(struct itimerspec, 32);
SIZE(struct itimerval, 32);
SIZE(struct timezone, 8);
SIZE(struct sockaddr_in, 16);
SIZE(struct sockaddr_in6, 28);
OFF(struct sockaddr_in6, sin6_addr, 8);
OFF(struct sockaddr_in6, sin6_scope_id, 24);
SIZE(struct sockaddr_un, 110);
SIZE(struct sockaddr_storage, 128);
SIZE(struct msghdr, 56);
OFF(struct msghdr, msg_iov, 16);
OFF(struct msghdr, msg_control, 32);
OFF(struct msghdr, msg_flags, 48);
SIZE(struct cmsghdr, 16);
OFF(struct cmsghdr, cmsg_type, 12);
SIZE(struct linger, 8);
SIZE(struct ip_mreq, 8);
SIZE(struct ipv6_mreq, 20);
SIZE(struct utsname, 390);
OFF(struct utsname, machine, 260);
OFF(struct utsname, domainname, 325);
SIZE(fd_set, 128);
SIZE(struct termios, 60);
OFF(struct termios, c_cc, 17);
SIZE(struct statfs, 120);
OFF(struct statfs, f_namelen, 64);
SIZE(fsid_t, 8);
SIZE(struct rlimit, 16);
SIZE(struct rusage, 144);
OFF(struct rusage, ru_maxrss, 32);
SIZE(struct sysinfo, 112);
OFF(struct sysinfo, mem_unit, 104);
SIZE(struct tms, 32);
SIZE(struct iovec, 16);
SIZE(struct inotify_event, 16);
OFF(struct inotify_event, name, 16);
SIZE(struct signalfd_siginfo, 128);
OFF(struct signalfd_siginfo, ssi_addr_lsb, 80);
SIZE(struct pollfd, 8);
SIZE(struct flock, 32);
OFF(struct flock, l_pid, 24);
SIZE(struct sched_param, 4);
SIZE(cpu_set_t, 128);

// Types.
SIZE(wint_t, 4);
SIZE(wchar_t, 4);
SIZE(clock_t, 8);
SIZE(time_t, 8);
SIZE(off_t, 8);
SIZE(ino_t, 8);
SIZE(dev_t, 8);
SIZE(mode_t, 4);
#if defined(__x86_64__)
SIZE(nlink_t, 8);
#else
SIZE(nlink_t, 4);
#endif
#if defined(__x86_64__)
SIZE(blksize_t, 8);
#else
SIZE(blksize_t, 4);
#endif
SIZE(blkcnt_t, 8);
SIZE(socklen_t, 4);
SIZE(sa_family_t, 2);
SIZE(in_port_t, 2);
SIZE(in_addr_t, 4);
SIZE(pid_t, 4);
SIZE(uid_t, 4);
SIZE(gid_t, 4);
SIZE(useconds_t, 4);
SIZE(suseconds_t, 8);
SIZE(id_t, 4);
SIZE(clockid_t, 4);
SIZE(timer_t, 8);
SIZE(pthread_t, 8);
SIZE(nfds_t, 8);
SIZE(div_t, 8);
SIZE(ldiv_t, 16);
SIZE(lldiv_t, 16);

// Widely shared library structures (same as glibc/musl).
#if defined(__x86_64__)
SIZE(jmp_buf, 200);
SIZE(sigjmp_buf, 200);
#else
SIZE(jmp_buf, 320);
SIZE(sigjmp_buf, 320);
#endif
SIZE(struct tm, 56);
OFF(struct tm, tm_gmtoff, 40);
OFF(struct tm, tm_zone, 48);
SIZE(struct addrinfo, 48);
OFF(struct addrinfo, ai_addr, 24);
OFF(struct addrinfo, ai_canonname, 32);
OFF(struct addrinfo, ai_next, 40);
SIZE(struct hostent, 32);
OFF(struct hostent, h_addr_list, 24);
SIZE(struct passwd, 48);
OFF(struct passwd, pw_shell, 40);
SIZE(struct group, 32);
OFF(struct group, gr_mem, 24);
SIZE(struct lconv, 96);
OFF(struct lconv, int_p_cs_precedes, 88);
SIZE(struct dl_phdr_info, 64);
OFF(struct dl_phdr_info, dlpi_phnum, 24);
OFF(struct dl_phdr_info, dlpi_tls_data, 56);
SIZE(ENTRY, 16);
SIZE(struct hsearch_data, 16);

// Library-private: must match the Rust definitions (asserted there).
SIZE(pthread_mutex_t, 20);
SIZE(pthread_cond_t, 16);
SIZE(pthread_rwlock_t, 16);
SIZE(pthread_barrier_t, 16);
SIZE(pthread_spinlock_t, 4);
SIZE(pthread_once_t, 4);
SIZE(pthread_key_t, 4);
SIZE(pthread_attr_t, 32);
SIZE(pthread_mutexattr_t, 4);
SIZE(pthread_condattr_t, 4);
SIZE(sem_t, 16);
SIZE(mtx_t, 20);
SIZE(cnd_t, 16);
SIZE(once_flag, 4);
SIZE(tss_t, 4);
SIZE(mbstate_t, 4);
SIZE(fpos_t, 8);

// Alignment of the lock types matters for the futex word.
_Static_assert(_Alignof(pthread_mutex_t) >= 4, "mutex alignment");
_Static_assert(_Alignof(pthread_cond_t) >= 4, "cond alignment");

int main(void) {
    // A few runtime checks that the headers and library agree on the
    // values baked into macros.
#if defined(__x86_64__)
    if (sizeof(struct stat) != 144) return 1;
#else
    if (sizeof(struct stat) != 128) return 1;
#endif
    struct stat st;
    if (stat("/", &st) != 0 || !S_ISDIR(st.st_mode)) return 2;
    struct rusage ru;
    if (getrusage(RUSAGE_SELF, &ru) != 0) return 3;
    struct sysinfo si;
    if (sysinfo(&si) != 0 || si.mem_unit == 0) return 4;
    return 0;
}
