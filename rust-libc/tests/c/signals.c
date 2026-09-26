// Signals: handlers, masks, raise, sigsuspend, sigwait, alarm, siginfo.
#include <errno.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

static volatile sig_atomic_t got;
static volatile sig_atomic_t got_info_sig;
static volatile pid_t info_pid;

static void handler(int sig) { got = sig; }
static void info_handler(int sig, siginfo_t *info, void *ctx) {
    (void)ctx;
    got_info_sig = sig;
    info_pid = info->si_pid;
}

int main(void) {
    CHECK(signal(SIGUSR1, handler) == SIG_DFL);
    CHECK(raise(SIGUSR1) == 0);
    CHECK(got == SIGUSR1);
    CHECK(signal(SIGUSR1, SIG_IGN) == handler);
    CHECK(raise(SIGUSR1) == 0 && got == SIGUSR1);

    struct sigaction sa, old;
    memset(&sa, 0, sizeof sa);
    sa.sa_sigaction = info_handler;
    sa.sa_flags = SA_SIGINFO;
    sigemptyset(&sa.sa_mask);
    CHECK(sigaction(SIGUSR2, &sa, &old) == 0);
    CHECK(old.sa_handler == SIG_DFL);
    CHECK(kill(getpid(), SIGUSR2) == 0);
    CHECK(got_info_sig == SIGUSR2 && info_pid == getpid());
    CHECK(sigaction(SIGUSR2, NULL, &old) == 0);
    CHECK(old.sa_sigaction == info_handler && (old.sa_flags & SA_SIGINFO));
    CHECK(sigaction(SIGKILL, &sa, NULL) == -1 && errno == EINVAL);
    CHECK(sigaction(0, &sa, NULL) == -1 && errno == EINVAL);

    // Blocking and pending.
    sigset_t set, oldset, pending;
    sigemptyset(&set);
    sigaddset(&set, SIGUSR1);
    CHECK(sigprocmask(SIG_BLOCK, &set, &oldset) == 0);
    CHECK(sigismember(&oldset, SIGUSR1) == 0);
    signal(SIGUSR1, handler);
    got = 0;
    CHECK(raise(SIGUSR1) == 0);
    CHECK(got == 0);
    CHECK(sigpending(&pending) == 0 && sigismember(&pending, SIGUSR1) == 1);
    CHECK(sigprocmask(SIG_UNBLOCK, &set, NULL) == 0);
    CHECK(got == SIGUSR1);

    // sigwait consumes a blocked signal.
    CHECK(sigprocmask(SIG_BLOCK, &set, NULL) == 0);
    CHECK(raise(SIGUSR1) == 0);
    int sig = 0;
    CHECK(sigwait(&set, &sig) == 0 && sig == SIGUSR1);
    CHECK(sigprocmask(SIG_SETMASK, &oldset, NULL) == 0);

    // alarm + sigsuspend.
    got = 0;
    signal(SIGALRM, handler);
    sigset_t block_alrm;
    sigemptyset(&block_alrm);
    sigaddset(&block_alrm, SIGALRM);
    CHECK(sigprocmask(SIG_BLOCK, &block_alrm, &oldset) == 0);
    CHECK(alarm(1) == 0);
    sigset_t none;
    sigemptyset(&none);
    CHECK(sigsuspend(&none) == -1 && errno == EINTR);
    CHECK(got == SIGALRM);
    CHECK(sigprocmask(SIG_SETMASK, &oldset, NULL) == 0);

    // Descriptions.
    CHECK(strcmp(strsignal(SIGSEGV), "Segmentation fault") == 0);
    psignal(SIGINT, "psignal");
    CHECK(killpg(0, 0) == 0 || errno != 0);
    // Parent/child signalling through a pipe of pids.
    pid_t child = fork();
    CHECK(child >= 0);
    if (child == 0) {
        pause();
        _exit(3);
    }
    usleep(20000);
    CHECK(kill(child, SIGTERM) == 0);
    int status;
    CHECK(waitpid(child, &status, 0) == child);
    CHECK(WIFSIGNALED(status) && WTERMSIG(status) == SIGTERM);
    return 0;
}
