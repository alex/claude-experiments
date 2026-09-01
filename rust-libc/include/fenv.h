#ifndef _FENV_H
#define _FENV_H
#include <bits/features.h>

#define FE_INVALID 1
#define FE_DIVBYZERO 4
#define FE_OVERFLOW 8
#define FE_UNDERFLOW 16
#define FE_INEXACT 32
#define FE_ALL_EXCEPT 63
#define FE_TONEAREST 0
#define FE_DOWNWARD 0x400
#define FE_UPWARD 0x800
#define FE_TOWARDZERO 0xc00

typedef unsigned short fexcept_t;
typedef struct {
    unsigned short __control_word, __unused1, __status_word, __unused2, __tags, __unused3;
    unsigned __eip, __cs_opcode, __data_offset, __data_selector;
    unsigned __mxcsr;
} fenv_t;

#define FE_DFL_ENV ((const fenv_t *)-1)

__BEGIN_DECLS
int feclearexcept(int);
int fegetexceptflag(fexcept_t *, int);
int feraiseexcept(int);
int fesetexceptflag(const fexcept_t *, int);
int fetestexcept(int);
int fegetround(void);
int fesetround(int);
int fegetenv(fenv_t *);
int feholdexcept(fenv_t *);
int fesetenv(const fenv_t *);
int feupdateenv(const fenv_t *);
__END_DECLS

#endif
