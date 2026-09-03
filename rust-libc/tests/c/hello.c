// The most basic smoke test: startup, write(2), exit status.
#include <string.h>
#include <unistd.h>

int main(int argc, char **argv) {
    const char *msg = "hello, world\n";
    if (write(1, msg, strlen(msg)) != (long)strlen(msg)) return 1;
    if (argc != 1) return 2;
    if (strlen(argv[0]) == 0) return 3;
    return 0;
}
