// <string.h>, <strings.h> and <ctype.h> through the real headers.
// -fno-builtin is not used, so this also checks that gcc's builtin
// lowering of memcpy/strlen/... links against our symbols.
#include <ctype.h>
#include <errno.h>
#include <string.h>
#include <strings.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

static char big[70000];

int main(void) {
    char buf[64];

    CHECK(strlen("") == 0);
    CHECK(strlen("hello") == 5);
    CHECK(strnlen("hello", 3) == 3);
    CHECK(strnlen("hello", 10) == 5);

    CHECK(strcmp("a", "a") == 0);
    CHECK(strcmp("a", "b") < 0);
    CHECK(strcmp("b", "a") > 0);
    CHECK(strcmp("abc", "ab") > 0);
    CHECK(strcmp("\xff", "\x01") > 0);  // unsigned comparison
    CHECK(strncmp("abcd", "abxx", 2) == 0);
    CHECK(strncmp("abcd", "abxx", 3) < 0);
    CHECK(strncmp("abc", "abc", 100) == 0);
    CHECK(strcasecmp("HeLLo", "hEllO") == 0);
    CHECK(strncasecmp("HeLLo1", "hEllO2", 5) == 0);
    CHECK(strncasecmp("HeLLo1", "hEllO2", 6) < 0);

    CHECK(strcpy(buf, "hello") == buf);
    CHECK(strcmp(buf, "hello") == 0);
    CHECK(strcat(buf, " world") == buf);
    CHECK(strcmp(buf, "hello world") == 0);
    volatile size_t one = 1;
    CHECK(strncat(buf, "!!!", one) == buf);
    CHECK(strcmp(buf, "hello world!") == 0);
    CHECK(stpcpy(buf, "abc") == buf + 3);
    memset(buf, 'x', sizeof buf);
    strncpy(buf, "ab", 5);
    CHECK(buf[0] == 'a' && buf[1] == 'b' && buf[2] == 0 && buf[3] == 0 && buf[4] == 0 && buf[5] == 'x');
    CHECK(strlcpy(buf, "hello", 3) == 5);
    CHECK(strcmp(buf, "he") == 0);
    CHECK(strlcat(buf, "llo", sizeof buf) == 5);
    CHECK(strcmp(buf, "hello") == 0);

    CHECK(strchr("hello", 'l') == "hello" + 2 || *strchr("hello", 'l') == 'l');
    const char *s = "hello world";
    CHECK(strchr(s, 'o') == s + 4);
    CHECK(strrchr(s, 'o') == s + 7);
    CHECK(strchr(s, '\0') == s + 11);
    CHECK(strchr(s, 'z') == NULL);
    CHECK(strchrnul(s, 'z') == s + 11);
    CHECK(strstr(s, "world") == s + 6);
    CHECK(strstr(s, "") == s);
    CHECK(strstr(s, "worlds") == NULL);
    CHECK(strspn(s, "hel") == 4);
    CHECK(strcspn(s, " ") == 5);
    CHECK(strpbrk(s, "dw") == s + 6);
    CHECK(memchr(s, 'w', 11) == s + 6);
    CHECK(memchr(s, 'w', 5) == NULL);
    CHECK(memrchr(s, 'o', 11) == s + 7);
    CHECK(memmem(s, 11, "lo w", 4) == s + 3);

    char tok[] = "  a b  c ";
    char *save;
    char *t = strtok_r(tok, " ", &save);
    CHECK(t && strcmp(t, "a") == 0);
    t = strtok_r(NULL, " ", &save);
    CHECK(t && strcmp(t, "b") == 0);
    t = strtok_r(NULL, " ", &save);
    CHECK(t && strcmp(t, "c") == 0);
    CHECK(strtok_r(NULL, " ", &save) == NULL);
    char tok2[] = "x:y";
    t = strtok(tok2, ":");
    CHECK(t && strcmp(t, "x") == 0);
    t = strtok(NULL, ":");
    CHECK(t && strcmp(t, "y") == 0);
    CHECK(strtok(NULL, ":") == NULL);
    char sep[] = "a,,b";
    char *sp = sep;
    CHECK(strcmp(strsep(&sp, ","), "a") == 0);
    CHECK(strcmp(strsep(&sp, ","), "") == 0);
    CHECK(strcmp(strsep(&sp, ","), "b") == 0);
    CHECK(strsep(&sp, ",") == NULL);

    CHECK(strcmp(strerror(ENOENT), "No such file or directory") == 0);
    CHECK(strcmp(strerror(12345), "Unknown error 12345") == 0);
    CHECK(strerror_r(EPERM, buf, sizeof buf) == 0);
    CHECK(strcmp(buf, "Operation not permitted") == 0);
    CHECK(strerror_r(EPERM, buf, 4) == ERANGE);
    CHECK(strcmp(buf, "Ope") == 0);

    // Large copies and compares exercise the rep movsb / vector paths.
    for (int i = 0; i < 70000; i++) big[i] = (char)(i * 7 + 1);
    static char big2[70000];
    memcpy(big2, big, sizeof big);
    CHECK(memcmp(big, big2, sizeof big) == 0);
    big2[69999] ^= 1;
    CHECK(memcmp(big, big2, sizeof big) != 0);
    CHECK(bcmp(big, big2, sizeof big) != 0);
    memmove(big + 1, big, 60000);
    CHECK(big[1] == (char)1 && big[60000] == (char)((59999 * 7 + 1) & 0xff));
    memset(big, 0, sizeof big);
    CHECK(big[0] == 0 && big[69999] == 0 && big[35000] == 0);
    bzero(big2, 10);
    CHECK(big2[9] == 0 && big2[10] != 0);
    explicit_bzero(big2, sizeof big2);
    CHECK(big2[69998] == 0);
    memset(big, 'a', 69999);
    CHECK(strlen(big) == 69999);
    CHECK(strchr(big, 'b') == NULL);
    big[50000] = 'b';
    CHECK(strchr(big, 'b') == big + 50000);
    CHECK(strrchr(big, 'a') == big + 69998);
    bcopy(big, big2, 100);
    CHECK(memcmp(big, big2, 100) == 0);
    CHECK(ffs(0) == 0 && ffs(1) == 1 && ffs(0x80) == 8 && ffsl(1L << 40) == 41 && ffsll(-1) == 1);

    CHECK(isalpha('a') && !isalpha('1') && isdigit('7') && isspace('\n') && !isspace('x'));
    CHECK(isupper('A') && !isupper('a') && islower('z') && isxdigit('f') && !isxdigit('g'));
    CHECK(ispunct('!') && isprint(' ') && !isprint('\n') && iscntrl('\n') && isgraph('a') && !isgraph(' '));
    CHECK(toupper('a') == 'A' && toupper('1') == '1' && tolower('Q') == 'q' && tolower(-1) == -1);
    CHECK(isalnum(-1) == 0 && isalpha(200) == 0);
    return 0;
}
