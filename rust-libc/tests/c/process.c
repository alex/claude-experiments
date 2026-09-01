// fork, exec, wait, system, atfork handlers and stdio across fork.
#include <errno.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

static int prepare_calls, parent_calls, child_calls;
static void prepare(void) { prepare_calls++; }
static void parent(void) { parent_calls++; }
static void child(void) { child_calls++; }

int main(void) {
    CHECK(pthread_atfork(prepare, parent, child) == 0);
    int fds[2];
    CHECK(pipe(fds) == 0);
    fflush(stdout);
    pid_t pid = fork();
    CHECK(pid >= 0);
    if (pid == 0) {
        close(fds[0]);
        if (child_calls != 1 || prepare_calls != 1 || parent_calls != 0) _exit(1);
        if (getppid() == getpid()) _exit(2);
        char msg[32];
        int n = snprintf(msg, sizeof msg, "child %d", getpid());
        write(fds[1], msg, n);
        _exit(42);
    }
    close(fds[1]);
    CHECK(prepare_calls == 1 && parent_calls == 1 && child_calls == 0);
    char buf[64];
    ssize_t n = read(fds[0], buf, sizeof buf - 1);
    CHECK(n > 0);
    buf[n] = 0;
    char expect[32];
    snprintf(expect, sizeof expect, "child %d", pid);
    CHECK(strcmp(buf, expect) == 0);
    int status;
    CHECK(waitpid(pid, &status, 0) == pid);
    CHECK(WIFEXITED(status) && WEXITSTATUS(status) == 42);
    close(fds[0]);

    // exec through the PATH and through an explicit path.
    pid = fork();
    if (pid == 0) {
        execlp("true", "true", (char *)NULL);
        _exit(127);
    }
    CHECK(waitpid(pid, &status, 0) == pid && WIFEXITED(status) && WEXITSTATUS(status) == 0);
    pid = fork();
    if (pid == 0) {
        execl("/bin/sh", "sh", "-c", "exit 7", (char *)NULL);
        _exit(127);
    }
    CHECK(wait(&status) == pid && WEXITSTATUS(status) == 7);
    pid = fork();
    if (pid == 0) {
        char *const argv[] = {"sh", "-c", "test \"$MARK\" = yes", NULL};
        char *const envp[] = {"MARK=yes", NULL};
        execve("/bin/sh", argv, envp);
        _exit(127);
    }
    CHECK(waitpid(pid, &status, 0) == pid && WEXITSTATUS(status) == 0);
    pid = fork();
    if (pid == 0) {
        char *const argv[] = {"definitely-not-a-command-xyz", NULL};
        execvp(argv[0], argv);
        _exit(errno == ENOENT ? 99 : 98);
    }
    CHECK(waitpid(pid, &status, 0) == pid && WEXITSTATUS(status) == 99);

    // system().
    CHECK(system(NULL) == 1);
    status = system("exit 5");
    CHECK(WIFEXITED(status) && WEXITSTATUS(status) == 5);
    status = system("echo from system");
    CHECK(status == 0);
    CHECK(waitpid(-1, &status, WNOHANG) == -1 && errno == ECHILD);

    // Buffered stdout survives fork correctly: data written before fork
    // is flushed once, not twice.
    printf("before fork\n");
    fflush(stdout);
    pid = fork();
    if (pid == 0) {
        printf("child says hi\n");
        exit(0);
    }
    CHECK(waitpid(pid, &status, 0) == pid && status == 0);
    printf("parent done\n");
    return 0;
}
