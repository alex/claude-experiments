// Differential test of the AArch64 instruction semantics of the Lean model
// (lean/ClaudeCrypto/Arm/Basic.lean) against a real implementation (hardware
// or QEMU).  Executes each modelled SIMD/crypto instruction, and SUBS, on
// pseudo-random inputs and prints one line per test:
//   <mnemonic> <inputs...> <outputs...>     (128-bit values as 32 hex digits)
// test/ArmInsnCheck.lean recomputes every output with the model and compares.
//
//   aarch64-linux-gnu-gcc -O1 -static -march=armv8-a+crypto arm_insn_test.c -o arm_insn_test
//   qemu-aarch64 -L /usr/aarch64-linux-gnu ./arm_insn_test > vectors.txt
#include <stdint.h>
#include <stdio.h>
#include <arm_neon.h>

static uint64_t st = 0x0123456789abcdefULL;
static uint64_t rnd(void) {
  st ^= st << 13; st ^= st >> 7; st ^= st << 17;
  return st;
}

static uint32x4_t rv(void) {
  uint64x2_t x = {rnd(), rnd()};
  return vreinterpretq_u32_u64(x);
}

static void pv(uint32x4_t v) {
  uint64x2_t x = vreinterpretq_u64_u32(v);
  printf(" %016llx%016llx", (unsigned long long)vgetq_lane_u64(x, 1),
         (unsigned long long)vgetq_lane_u64(x, 0));
}

#define SUBS(IMM)                                                              \
  do {                                                                         \
    uint64_t r, f;                                                             \
    __asm__ volatile("subs %0, %2, #" #IMM "\n\tmrs %1, nzcv"                  \
                     : "=r"(r), "=r"(f) : "r"(x) : "cc");                      \
    printf("subs %016llx %d %016llx %d\n", (unsigned long long)x, IMM,         \
           (unsigned long long)r, (int)(f >> 28));                             \
  } while (0)

int main(void) {
  for (int i = 0; i < 2000; i++) {
    uint32x4_t a = rv(), b = rv(), c = rv(), d;
    // SHA256H Qd, Qn, Vm.4S with d = a, n = b, m = c
    d = a; __asm__("sha256h %q0, %q1, %2.4s" : "+w"(d) : "w"(b), "w"(c));
    printf("sha256h"); pv(a); pv(b); pv(c); pv(d); printf("\n");
    d = a; __asm__("sha256h2 %q0, %q1, %2.4s" : "+w"(d) : "w"(b), "w"(c));
    printf("sha256h2"); pv(a); pv(b); pv(c); pv(d); printf("\n");
    d = a; __asm__("sha256su0 %0.4s, %1.4s" : "+w"(d) : "w"(b));
    printf("sha256su0"); pv(a); pv(b); pv(d); printf("\n");
    d = a; __asm__("sha256su1 %0.4s, %1.4s, %2.4s" : "+w"(d) : "w"(b), "w"(c));
    printf("sha256su1"); pv(a); pv(b); pv(c); pv(d); printf("\n");
    __asm__("rev32 %0.16b, %1.16b" : "=w"(d) : "w"(a));
    printf("rev32"); pv(a); pv(d); printf("\n");
    __asm__("add %0.4s, %1.4s, %2.4s" : "=w"(d) : "w"(a), "w"(b));
    printf("addv"); pv(a); pv(b); pv(d); printf("\n");
    uint64_t x = rnd();
    if (i % 4 == 0) x &= 0xfff;           // small values, to hit carries and zero
    if (i % 8 == 1) x = 0x8000000000000000ULL + (x & 0xfff);  // signed overflow
    switch (i % 5) {
      case 0: SUBS(0); break;
      case 1: SUBS(1); break;
      case 2: SUBS(64); break;
      case 3: SUBS(2048); break;
      default: SUBS(4095); break;
    }
  }
  return 0;
}
