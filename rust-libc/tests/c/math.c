// <math.h> and <fenv.h>.
#include <fenv.h>
#include <math.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#define CHECK(cond) do { if (!(cond)) { const char *m = "FAIL: " #cond "\n"; write(2, m, strlen(m)); return __LINE__; } } while (0)
#define NEAR(a, b) (fabs((a) - (b)) < 1e-12)

int main(void) {
    CHECK(sqrt(2.0) * sqrt(2.0) - 2.0 < 1e-15);
    CHECK(NEAR(sin(M_PI_2), 1.0) && NEAR(cos(0.0), 1.0) && NEAR(tan(M_PI_4), 1.0));
    CHECK(NEAR(exp(1.0), M_E) && NEAR(log(M_E), 1.0) && NEAR(log10(1000.0), 3.0) && NEAR(log2(8.0), 3.0));
    CHECK(pow(2.0, 0.5) == sqrt(2.0) && NEAR(cbrt(27.0), 3.0) && NEAR(hypot(3.0, 4.0), 5.0));
    CHECK(floor(-1.5) == -2.0 && ceil(-1.5) == -1.0 && trunc(-1.5) == -1.0 && round(2.5) == 3.0 && rint(2.5) == 2.0);
    CHECK(fmod(7.0, 3.0) == 1.0 && remainder(7.0, 3.0) == 1.0 && fabs(-3.0) == 3.0 && copysign(1.0, -0.0) == -1.0);
    CHECK(fmax(1.0, 2.0) == 2.0 && fmin(1.0, 2.0) == 1.0 && fdim(3.0, 1.0) == 2.0 && fma(2.0, 3.0, 1.0) == 7.0);
    CHECK(NEAR(atan2(1.0, 1.0), M_PI_4) && NEAR(asin(1.0), M_PI_2) && NEAR(acos(1.0), 0.0));
    CHECK(NEAR(sinh(0.0), 0.0) && NEAR(cosh(0.0), 1.0) && NEAR(tanh(0.0), 0.0) && NEAR(asinh(0.0), 0.0));
    CHECK(NEAR(tgamma(5.0), 24.0) && NEAR(lgamma(1.0), 0.0) && NEAR(erf(0.0), 0.0) && NEAR(erfc(0.0), 1.0));
    CHECK(NEAR(expm1(0.0), 0.0) && NEAR(log1p(0.0), 0.0) && NEAR(exp2(3.0), 8.0));
    int e;
    CHECK(frexp(8.0, &e) == 0.5 && e == 4 && ldexp(0.5, 4) == 8.0 && scalbn(1.0, 3) == 8.0 && ilogb(8.0) == 3 && logb(8.0) == 3.0);
    double ip;
    CHECK(modf(3.25, &ip) == 0.25 && ip == 3.0);
    int q;
    CHECK(remquo(7.0, 2.0, &q) == -1.0 && q == 4);
    CHECK(lround(2.5) == 3 && lround(-2.5) == -3 && llround(1e10) == 10000000000LL && lrint(2.5) == 2 && llrint(3.5) == 4);
    CHECK(nearbyint(2.5) == 2.0 && nextafter(1.0, 2.0) > 1.0 && nextafter(1.0, 2.0) - 1.0 < 3e-16);
    CHECK(isnan(nan("")) && isinf(HUGE_VAL) && !isfinite(INFINITY) && isfinite(1.0) && signbit(-0.0) && !signbit(0.0));
    CHECK(fpclassify(0.0) == FP_ZERO && fpclassify(1e-310) == FP_SUBNORMAL && fpclassify(1.0) == FP_NORMAL && fpclassify(NAN) == FP_NAN);
    CHECK(isnan(sqrt(-1.0)) && isinf(log(0.0)) && log(0.0) < 0);
    CHECK(sinf(0.0f) == 0.0f && sqrtf(4.0f) == 2.0f && powf(2.0f, 3.0f) == 8.0f && fabsf(-1.5f) == 1.5f && floorf(1.5f) == 1.0f);
    CHECK(NEAR(j0(0.0), 1.0) && NEAR(y0(1.0), 0.08825696421567696) && NEAR(jn(2, 0.0), 0.0));
    double s, c;
    sincos(M_PI, &s, &c);
    CHECK(fabs(s) < 1e-15 && NEAR(c, -1.0));
    CHECK(isgreater(2.0, 1.0) && isless(1.0, 2.0) && isunordered(NAN, 1.0) && !islessgreater(1.0, 1.0));

    // Rounding modes and exception flags.
    CHECK(fegetround() == FE_TONEAREST);
    CHECK(fesetround(FE_UPWARD) == 0 && fegetround() == FE_UPWARD);
    volatile double third = 1.0 / 3.0;
    volatile double one = 1.0;
    volatile double x = one / 3.0;
    CHECK(x >= third);
    CHECK(fesetround(FE_DOWNWARD) == 0);
    volatile double y = one / 3.0;
    CHECK(y <= x);
    CHECK(fesetround(FE_TONEAREST) == 0);
    CHECK(feclearexcept(FE_ALL_EXCEPT) == 0 && fetestexcept(FE_ALL_EXCEPT) == 0);
    volatile double zero = 0.0;
    volatile double inf = one / zero;
    CHECK(isinf(inf) && (fetestexcept(FE_DIVBYZERO) & FE_DIVBYZERO));
    CHECK(feclearexcept(FE_DIVBYZERO) == 0 && fetestexcept(FE_DIVBYZERO) == 0);
    fenv_t env;
    CHECK(fegetenv(&env) == 0 && feraiseexcept(FE_INEXACT) == 0 && fetestexcept(FE_INEXACT));
    CHECK(fesetenv(&env) == 0 && fetestexcept(FE_INEXACT) == 0);
    CHECK(fesetenv(FE_DFL_ENV) == 0 && fegetround() == FE_TONEAREST);
    printf("%.3f %.3f %g\n", sin(1.0), exp(2.0), pow(10.0, -3.0));
    return 0;
}
