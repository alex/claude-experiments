#ifndef _CTYPE_H
#define _CTYPE_H
#include <bits/features.h>

/* glibc's class bits, for code compiled against its <ctype.h> macros and
   for libstdc++'s ctype<char>. */
enum {
    _ISupper = 0x100, _ISlower = 0x200, _ISalpha = 0x400, _ISdigit = 0x800,
    _ISxdigit = 0x1000, _ISspace = 0x2000, _ISprint = 0x4000, _ISgraph = 0x8000,
    _ISblank = 0x1, _IScntrl = 0x2, _ISpunct = 0x4, _ISalnum = 0x8
};

__BEGIN_DECLS
const unsigned short **__ctype_b_loc(void);
const int **__ctype_tolower_loc(void);
const int **__ctype_toupper_loc(void);

int isalnum(int);
int isalpha(int);
int isblank(int);
int iscntrl(int);
int isdigit(int);
int isgraph(int);
int islower(int);
int isprint(int);
int ispunct(int);
int isspace(int);
int isupper(int);
int isxdigit(int);
int isascii(int);
int tolower(int);
int toupper(int);
int toascii(int);

__END_DECLS

#endif
