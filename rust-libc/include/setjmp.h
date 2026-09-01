#ifndef _SETJMP_H
#define _SETJMP_H
#include <bits/features.h>

typedef struct __jmp_buf_tag {
    unsigned long __jb[8];
    unsigned long __fl;
    unsigned long __ss[16];
} jmp_buf[1];
typedef jmp_buf sigjmp_buf;

__BEGIN_DECLS

int setjmp(jmp_buf);
int _setjmp(jmp_buf);
int sigsetjmp(sigjmp_buf, int);
__NORETURN void longjmp(jmp_buf, int);
__NORETURN void _longjmp(jmp_buf, int);
__NORETURN void siglongjmp(sigjmp_buf, int);

#define setjmp setjmp

__END_DECLS

#endif
