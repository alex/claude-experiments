// A failed assertion prints a diagnostic and aborts.
// expect-signal: SIGABRT
#include <assert.h>
#include <stdio.h>

int main(int argc, char **argv) {
    (void)argv;
    assert(argc == 1);
    assert(argc == 2);
    puts("not reached");
    return 0;
}
