#ifndef _MATH_H
#define _MATH_H
#include <bits/features.h>

#define HUGE_VAL __builtin_huge_val()
#define HUGE_VALF __builtin_huge_valf()
#define HUGE_VALL __builtin_huge_vall()
#define INFINITY __builtin_inff()
#define NAN __builtin_nanf("")

#define FP_NAN 0
#define FP_INFINITE 1
#define FP_ZERO 2
#define FP_SUBNORMAL 3
#define FP_NORMAL 4

#define fpclassify(x) __builtin_fpclassify(FP_NAN, FP_INFINITE, FP_NORMAL, FP_SUBNORMAL, FP_ZERO, x)
#define isnan(x) __builtin_isnan(x)
#define isinf(x) __builtin_isinf_sign(x)
#define isfinite(x) __builtin_isfinite(x)
#define isnormal(x) __builtin_isnormal(x)
#define signbit(x) __builtin_signbit(x)
#define isgreater(x, y) __builtin_isgreater(x, y)
#define isgreaterequal(x, y) __builtin_isgreaterequal(x, y)
#define isless(x, y) __builtin_isless(x, y)
#define islessequal(x, y) __builtin_islessequal(x, y)
#define islessgreater(x, y) __builtin_islessgreater(x, y)
#define isunordered(x, y) __builtin_isunordered(x, y)

#define MATH_ERRNO 1
#define MATH_ERREXCEPT 2
#define math_errhandling MATH_ERREXCEPT
#define FP_ILOGB0 (-2147483647 - 1)
#define FP_ILOGBNAN (-2147483647 - 1)

#define M_E 2.7182818284590452354
#define M_LOG2E 1.4426950408889634074
#define M_LOG10E 0.43429448190325182765
#define M_LN2 0.69314718055994530942
#define M_LN10 2.30258509299404568402
#define M_PI 3.14159265358979323846
#define M_PI_2 1.57079632679489661923
#define M_PI_4 0.78539816339744830962
#define M_1_PI 0.31830988618379067154
#define M_2_PI 0.63661977236758134308
#define M_2_SQRTPI 1.12837916709551257390
#define M_SQRT2 1.41421356237309504880
#define M_SQRT1_2 0.70710678118654752440

typedef double double_t;
typedef float float_t;

__BEGIN_DECLS

extern int signgam;

#define __MATH1(n) double n(double); float n##f(float);
#define __MATH2(n) double n(double, double); float n##f(float, float);
__MATH1(acos) __MATH1(acosh) __MATH1(asin) __MATH1(asinh) __MATH1(atan) __MATH1(atanh)
__MATH1(cbrt) __MATH1(ceil) __MATH1(cos) __MATH1(cosh) __MATH1(erf) __MATH1(erfc)
__MATH1(exp) __MATH1(exp10) __MATH1(exp2) __MATH1(expm1) __MATH1(fabs) __MATH1(floor)
__MATH1(j0) __MATH1(j1) __MATH1(lgamma) __MATH1(log) __MATH1(log10) __MATH1(log1p)
__MATH1(log2) __MATH1(logb) __MATH1(nearbyint) __MATH1(rint) __MATH1(round) __MATH1(sin)
__MATH1(sinh) __MATH1(sqrt) __MATH1(tan) __MATH1(tanh) __MATH1(tgamma) __MATH1(trunc)
__MATH1(y0) __MATH1(y1)
__MATH2(atan2) __MATH2(copysign) __MATH2(fdim) __MATH2(fmax) __MATH2(fmin) __MATH2(fmod)
__MATH2(hypot) __MATH2(nextafter) __MATH2(pow) __MATH2(remainder)
#undef __MATH1
#undef __MATH2

double fma(double, double, double);
float fmaf(float, float, float);
double frexp(double, int *);
float frexpf(float, int *);
double ldexp(double, int);
float ldexpf(float, int);
double scalbn(double, int);
float scalbnf(float, int);
double scalbln(double, long);
float scalblnf(float, long);
int ilogb(double);
int ilogbf(float);
double modf(double, double *);
float modff(float, float *);
double remquo(double, double, int *);
float remquof(float, float, int *);
double jn(int, double);
float jnf(int, float);
double yn(int, double);
float ynf(int, float);
double lgamma_r(double, int *);
float lgammaf_r(float, int *);
void sincos(double, double *, double *);
void sincosf(float, float *, float *);
long lround(double);
long lroundf(float);
long long llround(double);
long long llroundf(float);
long lrint(double);
long lrintf(float);
long long llrint(double);
long long llrintf(float);
double nan(const char *);
float nanf(const char *);
double significand(double);
double pow10(double);
double drem(double, double);
double gamma(double);
int finite(double);
int finitef(float);

__END_DECLS

#endif
