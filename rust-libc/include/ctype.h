#ifndef _CTYPE_H
#define _CTYPE_H
#include <bits/features.h>

__BEGIN_DECLS

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
