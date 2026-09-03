// File streams: fopen/fread/fwrite/fseek/fgets/getline/ungetc/scanf.
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

int main(void) {
    const char *name = "stdio_file.tmp";
    FILE *f = fopen(name, "w");
    CHECK(f != NULL);
    CHECK(fprintf(f, "line %d\n", 1) == 7);
    CHECK(fputs("line 2\n", f) == 1);
    CHECK(fwrite("line 3\n", 1, 7, f) == 7);
    for (int i = 0; i < 20000; i++) CHECK(fputc('a' + i % 26, f) == 'a' + i % 26);
    CHECK(fputc('\n', f) == '\n');
    CHECK(ftell(f) == 21 + 20001);
    CHECK(fclose(f) == 0);

    f = fopen(name, "r");
    CHECK(f != NULL);
    char line[64];
    CHECK(fgets(line, sizeof line, f) != NULL && strcmp(line, "line 1\n") == 0);
    int c = fgetc(f);
    CHECK(c == 'l');
    CHECK(ungetc('L', f) == 'L');
    CHECK(fgets(line, sizeof line, f) != NULL && strcmp(line, "Line 2\n") == 0);
    CHECK(ftell(f) == 14);
    int num = 0;
    char word[16];
    CHECK(fscanf(f, "%s %d", word, &num) == 2);
    CHECK(strcmp(word, "line") == 0 && num == 3);
    CHECK(fgetc(f) == '\n');
    char *big = NULL;
    size_t cap = 0;
    ssize_t n = getline(&big, &cap, f);
    CHECK(n == 20001);
    CHECK(big[0] == 'a' && big[25] == 'z' && big[20000] == '\n' && big[20001] == 0);
    free(big);
    CHECK(fgetc(f) == EOF);
    CHECK(feof(f) == 1);
    CHECK(fseek(f, 5, SEEK_SET) == 0);
    CHECK(feof(f) == 0);
    CHECK(fgetc(f) == '1');
    CHECK(fseek(f, -2, SEEK_CUR) == 0);
    CHECK(fgetc(f) == ' ');
    CHECK(fseek(f, -6, SEEK_END) == 0);
    CHECK(fgetc(f) == 'a' + 19995 % 26);
    rewind(f);
    char buf[8];
    CHECK(fread(buf, 1, 4, f) == 4 && memcmp(buf, "line", 4) == 0);
    CHECK(fread(buf, 3, 2, f) == 2 && memcmp(buf, " 1\nlin", 6) == 0);
    CHECK(fclose(f) == 0);

    // Read/write on the same stream and append mode.
    f = fopen(name, "r+");
    CHECK(f != NULL);
    CHECK(fseek(f, 0, SEEK_END) == 0);
    long end = ftell(f);
    CHECK(fputs("tail", f) == 1);
    CHECK(fflush(f) == 0);
    CHECK(fseek(f, end, SEEK_SET) == 0);
    CHECK(fread(buf, 1, 4, f) == 4 && memcmp(buf, "tail", 4) == 0);
    CHECK(fclose(f) == 0);
    f = fopen(name, "a");
    CHECK(f != NULL);
    CHECK(fputs("!", f) == 1);
    CHECK(fclose(f) == 0);
    f = fopen(name, "r");
    CHECK(fseek(f, -5, SEEK_END) == 0);
    CHECK(fread(buf, 1, 5, f) == 5 && memcmp(buf, "tail!", 5) == 0);
    CHECK(fclose(f) == 0);

    // Errors.
    CHECK(fopen("/nonexistent/dir/file", "r") == NULL && errno == ENOENT);
    CHECK(fopen(name, "q") == NULL && errno == EINVAL);
    f = fopen(name, "r");
    CHECK(fputc('x', f) == EOF && ferror(f));
    clearerr(f);
    CHECK(ferror(f) == 0);
    CHECK(fclose(f) == 0);
    CHECK(remove(name) == 0);
    CHECK(remove(name) == -1 && errno == ENOENT);

    // sscanf.
    int a, b;
    char s[16];
    CHECK(sscanf("10 20 abc", "%d %d %s", &a, &b, s) == 3 && a == 10 && b == 20 && strcmp(s, "abc") == 0);
    double d;
    CHECK(sscanf("3.5e2", "%lf", &d) == 1 && d == 350.0);
    CHECK(sscanf("", "%d", &a) == EOF);
    CHECK(sscanf("x", "%d", &a) == 0);
    unsigned hex;
    CHECK(sscanf("ff", "%x", &hex) == 1 && hex == 255);
    CHECK(sscanf("key=val", "%[^=]=%s", s, word) == 2 && strcmp(s, "key") == 0 && strcmp(word, "val") == 0);
    int consumed = 0;
    CHECK(sscanf("123 456", "%d%n", &a, &consumed) == 1 && consumed == 3);
    long double ld;
    CHECK(sscanf("2.5", "%Lf", &ld) == 1 && ld == 2.5L);

    // Memory streams.
    char *mem = NULL;
    size_t memsize = 0;
    f = open_memstream(&mem, &memsize);
    CHECK(f != NULL);
    fprintf(f, "%d-%s", 7, "seven");
    CHECK(fclose(f) == 0);
    CHECK(memsize == 7 && strcmp(mem, "7-seven") == 0);
    free(mem);
    char fixed[] = "12 34";
    f = fmemopen(fixed, sizeof fixed - 1, "r");
    CHECK(fscanf(f, "%d %d", &a, &b) == 2 && a == 12 && b == 34);
    CHECK(fclose(f) == 0);

    // tmpfile and setvbuf.
    f = tmpfile();
    CHECK(f != NULL);
    CHECK(setvbuf(f, NULL, _IONBF, 0) == 0);
    CHECK(fputs("unbuffered", f) == 1);
    rewind(f);
    CHECK(fgets(line, sizeof line, f) != NULL && strcmp(line, "unbuffered") == 0);
    CHECK(fclose(f) == 0);

    // stdout is fully buffered when not a tty: this output must still
    // arrive at exit.
    printf("done\n");
    return 0;
}
