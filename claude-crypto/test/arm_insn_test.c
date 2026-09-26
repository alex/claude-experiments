// Differential test of the AArch64 instruction semantics of the Lean model
// (lean/ClaudeCrypto/Arm/Basic.lean) against a real implementation (hardware
// or QEMU).  Executes each modelled SIMD/crypto instruction and each scalar
// integer instruction (with random input flags, printing the output flags as
// an NZCV nibble) on pseudo-random inputs and prints one line per test:
//   <mnemonic> <inputs...> <outputs...>     (128-bit values as 32 hex digits)
// test/ArmInsnCheck.lean recomputes every output with the model and compares.
//
//   aarch64-linux-gnu-gcc -O1 -static -march=armv8-a+crypto arm_insn_test.c -o arm_insn_test
//   qemu-aarch64 -L /usr/aarch64-linux-gnu ./arm_insn_test > vectors.txt
#include <stdint.h>
#include <stdio.h>
#include <string.h>
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

/* Scalar instructions: x1 = x, x2 = y, NZCV = nzcv (a nibble) on entry;
   prints "<name> <x> <y> <nzcv in> <result> <nzcv out>". */
#define SCALAR(NAME, INSN)                                                     \
  do {                                                                         \
    uint64_t r = 0x5555, f, fi = (uint64_t)nzcv << 28;                         \
    __asm__ volatile("msr nzcv, %3\n\t" INSN "\n\tmrs %1, nzcv"                \
                     : "+r"(r), "=r"(f) : "r"(x), "r"(fi), "r"(y) : "cc");    \
    printf(NAME " %016llx %016llx %d %016llx %d\n", (unsigned long long)x,      \
           (unsigned long long)y, nzcv, (unsigned long long)r, (int)(f >> 28));  \
  } while (0)
/* operands: %0 = result (initially 0x5555), %2 = x, %4 = y */

#define SHIFTS(OP, SH) SCALAR(#OP " " #SH, #OP " %0, %2, #" #SH)
#define MOVK(IMM, HW)                                                          \
  do { uint64_t xx = x; x = r0;                                                \
    SCALAR("movk " #IMM " " #HW, "mov %0, %2\n\tmovk %0, #" #IMM ", lsl #" #HW "*16"); \
    x = xx; } while (0)
#define MOVZ(IMM, HW) SCALAR("movz " #IMM " " #HW, "movz %0, #" #IMM ", lsl #" #HW "*16")

static unsigned char buf[64], buf2[64];
static void pbuf(const unsigned char *b) {
  printf(" ");
  for (int i = 0; i < 64; i++) printf("%02x", b[i]);
}

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
    uint64_t y = rnd(), r0 = rnd();
    if (i % 4 == 1) y = x;                    // equal operands
    if (i % 4 == 2) y = ~x;                   // carries all the way
    if (i % 8 == 3) y = x + 1;
    int nzcv = (int)(rnd() & 15);
    SCALAR("adds", "adds %0, %2, %4");
    SCALAR("adcs", "adcs %0, %2, %4");
    SCALAR("subs", "subs %0, %2, %4");
    SCALAR("sbcs", "sbcs %0, %2, %4");
    SCALAR("addr", "add %0, %2, %4");
    SCALAR("subr", "sub %0, %2, %4");
    SCALAR("mul", "mul %0, %2, %4");
    SCALAR("umulh", "umulh %0, %2, %4");
    SCALAR("and", "and %0, %2, %4");
    SCALAR("orr", "orr %0, %2, %4");
    SCALAR("eor", "eor %0, %2, %4");
    SCALAR("rev", "rev %0, %2");
    SCALAR("csetm eq", "csetm %0, eq");
    SCALAR("csetm ne", "csetm %0, ne");
    SCALAR("csetm hs", "csetm %0, hs");
    SCALAR("csetm lo", "csetm %0, lo");
    SCALAR("csetm hi", "csetm %0, hi");
    SCALAR("csetm ls", "csetm %0, ls");
    switch (i % 8) {
      case 0: SHIFTS(lsl, 0); SHIFTS(lsr, 0); MOVZ(0, 0); MOVK(0, 0); break;
      case 1: SHIFTS(lsl, 1); SHIFTS(lsr, 1); MOVZ(1, 1); MOVK(1, 1); break;
      case 2: SHIFTS(lsl, 13); SHIFTS(lsr, 13); MOVZ(0xffff, 2); MOVK(0xffff, 2); break;
      case 3: SHIFTS(lsl, 32); SHIFTS(lsr, 32); MOVZ(0x8001, 3); MOVK(0x8001, 3); break;
      case 4: SHIFTS(lsl, 63); SHIFTS(lsr, 63); MOVZ(0x1234, 0); MOVK(0x1234, 1); break;
      case 5: SHIFTS(lsl, 7); SHIFTS(lsr, 56); MOVZ(0xabcd, 1); MOVK(0xabcd, 3); break;
      case 6: SHIFTS(lsl, 48); SHIFTS(lsr, 16); MOVZ(0x7fff, 3); MOVK(0x7fff, 0); break;
      default: SHIFTS(lsl, 62); SHIFTS(lsr, 3); MOVZ(0xfffe, 2); MOVK(0, 3); break;
    }
    // 64-bit loads and stores into a 64-byte buffer (the model places it at 0x1000)
    for (int k = 0; k < 64; k += 8) {
      uint64_t w = rnd();
      memcpy(buf + k, &w, 8);
    }
    uint64_t r, off = rnd() % 57;             // register offsets need not be aligned
#define LDRI(OFF)                                                              \
    __asm__ volatile("ldr %0, [%1, #" #OFF "]" : "=r"(r) : "r"(buf) : "memory"); \
    printf("ldr"); pbuf(buf); printf(" %d %016llx\n", OFF, (unsigned long long)r)
#define STRI(OFF)                                                              \
    memcpy(buf2, buf, 64);                                                     \
    __asm__ volatile("str %1, [%0, #" #OFF "]" : : "r"(buf2), "r"(y) : "memory"); \
    printf("str"); pbuf(buf); printf(" %d %016llx", OFF, (unsigned long long)y); \
    pbuf(buf2); printf("\n")
    switch (i % 4) {
      case 0: LDRI(0); STRI(56); break;
      case 1: LDRI(8); STRI(16); break;
      case 2: LDRI(48); STRI(0); break;
      default: LDRI(56); STRI(40); break;
    }
    __asm__ volatile("ldr %0, [%1, %2]" : "=r"(r) : "r"(buf), "r"(off) : "memory");
    printf("ldrr"); pbuf(buf); printf(" %d %016llx\n", (int)off, (unsigned long long)r);
    memcpy(buf2, buf, 64);
    __asm__ volatile("str %2, [%0, %1]" : : "r"(buf2), "r"(off), "r"(y) : "memory");
    printf("strr"); pbuf(buf); printf(" %d %016llx", (int)off, (unsigned long long)y);
    pbuf(buf2); printf("\n");
  }
  return 0;
}
