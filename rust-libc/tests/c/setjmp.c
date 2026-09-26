// setjmp/longjmp and sigsetjmp/siglongjmp with mask restoration.
// cflags: -Wno-infinite-recursion
#include <setjmp.h>
#include <signal.h>
#include <string.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

static jmp_buf jb;
static sigjmp_buf sjb;
static int depth;

__attribute__((noreturn)) static void jump(int v) { longjmp(jb, v); }
static void recurse(int n) {
    if (n == 0) jump(9);
    depth = n;
    recurse(n - 1);
}

int main(void) {
    volatile int count = 0;
    int r = setjmp(jb);
    count++;
    if (r == 0) {
        jump(5);
        return 1;
    }
    CHECK(r == 5 && count == 2);
    r = setjmp(jb);
    if (r == 0) longjmp(jb, 0);  // a zero value becomes 1
    CHECK(r == 1);
    r = setjmp(jb);
    if (r == 0) recurse(50);
    CHECK(r == 9 && depth == 1);

    // sigsetjmp saves and restores the signal mask.
    sigset_t set, cur;
    sigemptyset(&set);
    sigaddset(&set, SIGUSR1);
    sigprocmask(SIG_SETMASK, &set, NULL);  // USR1 blocked
    r = sigsetjmp(sjb, 1);
    if (r == 0) {
        sigemptyset(&set);
        sigprocmask(SIG_SETMASK, &set, NULL);  // unblock everything
        siglongjmp(sjb, 3);
    }
    CHECK(r == 3);
    sigprocmask(SIG_BLOCK, NULL, &cur);
    CHECK(sigismember(&cur, SIGUSR1) == 1);  // restored: blocked again
    // Without savemask the mask stays as changed.
    r = sigsetjmp(sjb, 0);
    if (r == 0) {
        sigemptyset(&set);
        sigprocmask(SIG_SETMASK, &set, NULL);
        siglongjmp(sjb, 4);
    }
    CHECK(r == 4);
    sigprocmask(SIG_BLOCK, NULL, &cur);
    CHECK(sigismember(&cur, SIGUSR1) == 0);
    return 0;
}
