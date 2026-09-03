// Wide characters, multibyte conversion, locale and wctype.
#include <langinfo.h>
#include <locale.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <wchar.h>
#include <wctype.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)

int main(void) {
    CHECK(strcmp(setlocale(LC_ALL, NULL), "C") == 0);
    CHECK(setlocale(LC_ALL, "C.UTF-8") != NULL && strcmp(nl_langinfo(CODESET), "UTF-8") == 0);
    CHECK(setlocale(LC_ALL, "") != NULL);
    CHECK(localeconv()->decimal_point[0] == '.');

    const char *utf8 = "héllo 世界";
    wchar_t wide[32];
    size_t n = mbstowcs(wide, utf8, 32);
    CHECK(n == 8 && wide[1] == 0xe9 && wide[6] == 0x4e16 && wide[8] == 0);
    CHECK(wcslen(wide) == 8 && wcwidth(wide[6]) == 2 && wcwidth(L'a') == 1 && wcswidth(wide, 8) == 10);
    char back[64];
    CHECK(wcstombs(back, wide, sizeof back) == (size_t)strlen(utf8) && strcmp(back, utf8) == 0);
    wchar_t wc;
    mbstate_t st;
    memset(&st, 0, sizeof st);
    CHECK(mbrtowc(&wc, "€", 3, &st) == 3 && wc == 0x20ac);
    CHECK(mbrtowc(&wc, "€", 1, &st) == (size_t)-2 && mbrtowc(&wc, "€" + 1, 2, &st) == 2 && wc == 0x20ac);
    char mb[MB_CUR_MAX];
    CHECK(wcrtomb(mb, 0x1f389, NULL) == 4 && (unsigned char)mb[0] == 0xf0);
    CHECK(mblen("é", 2) == 2 && mblen("a", 1) == 1);
    CHECK(btowc('a') == L'a' && wctob(L'a') == 'a' && wctob(0x20ac) == EOF);

    wchar_t buf[32];
    wcscpy(buf, L"hello");
    wcscat(buf, L" world");
    CHECK(wcscmp(buf, L"hello world") == 0 && wcsncmp(buf, L"help", 3) == 0 && wcscmp(buf, L"help") < 0);
    CHECK(wcschr(buf, L'o') == buf + 4 && wcsrchr(buf, L'o') == buf + 7 && wcsstr(buf, L"wor") == buf + 6);
    CHECK(wcsspn(buf, L"hel") == 4 && wcscspn(buf, L"w") == 6 && wcspbrk(buf, L"dw") == buf + 6);
    wchar_t *save;
    wchar_t tok[] = L"a,b,,c";
    CHECK(wcscmp(wcstok(tok, L",", &save), L"a") == 0 && wcscmp(wcstok(NULL, L",", &save), L"b") == 0);
    CHECK(wcscmp(wcstok(NULL, L",", &save), L"c") == 0 && wcstok(NULL, L",", &save) == NULL);
    wchar_t *d = wcsdup(L"dup");
    CHECK(wcscmp(d, L"dup") == 0);
    free(d);
    wmemset(buf, L'x', 3);
    buf[3] = 0;
    CHECK(wcscmp(buf, L"xxx") == 0 && wmemcmp(buf, L"xxy", 3) < 0 && wmemchr(buf, L'x', 3) == buf);
    CHECK(wcstol(L"  -42z", NULL, 10) == -42 && wcstoul(L"ff", NULL, 16) == 255 && wcstod(L"2.5e1", NULL) == 25.0);
    CHECK(wcscasecmp(L"HeLLo", L"hello") == 0 && wcsncasecmp(L"HeLLo", L"help", 3) == 0);

    CHECK(iswalpha(L'é') && iswalpha(L'世') && !iswalpha(L'1') && iswdigit(L'5') && !iswdigit(L'٣'));
    CHECK(iswupper(L'Ä') && iswlower(L'ä') && towupper(L'é') == L'É' && towlower(L'É') == L'é');
    CHECK(iswspace(L' ') && iswspace(L'　') && iswpunct(L'!') && iswxdigit(L'f') && !iswxdigit(L'g') && iswcntrl(L'\n'));
    CHECK(iswctype(L'a', wctype("alpha")) && !iswctype(L'a', wctype("digit")) && wctype("bogus") == 0);
    CHECK(towctrans(L'a', wctrans("toupper")) == L'A');

    wchar_t out[64];
    int len = swprintf(out, 64, L"%d-%s-%ls", 7, "narrow", L"wïde");
    CHECK(len == 13 && wcscmp(out, L"7-narrow-wïde") == 0);
    CHECK(swprintf(out, 4, L"%s", "toolong") < 0);

    // Wide stdio through a memory stream.
    char *mem = NULL;
    size_t memsize = 0;
    FILE *f = open_memstream(&mem, &memsize);
    CHECK(fputws(L"wide 世", f) == 0 && fputwc(L'!', f) == L'!');
    fclose(f);
    CHECK(strcmp(mem, "wide 世!") == 0);
    f = fmemopen(mem, memsize, "r");
    CHECK(fgetwc(f) == L'w' && fgetws(out, 64, f) != NULL && wcscmp(out, L"ide 世!") == 0 && fgetwc(f) == WEOF);
    fclose(f);
    free(mem);
    printf("%ls|%lc\n", L"é世", (wint_t)0x1f389);
    return 0;
}
