// Differential test of the ppc64le instruction semantics of the Lean model
// (lean/ClaudeCrypto/Ppc/Basic.lean) against a real implementation (hardware
// or QEMU).  Executes each modelled instruction on pseudo-random inputs and
// prints one line per test:
//   <mnemonic> [<immediates>] <inputs...> <outputs...>
// test/PpcInsnCheck.lean recomputes every output with the model and compares.
//
// Vector registers are transferred with lvx/stvx, which in little-endian mode
// move a 16-byte aligned quadword as a little-endian 128-bit integer (the byte
// at the lowest address is the least significant byte, ISA byte 15).  Vector
// values are printed as that 128-bit integer (32 hex digits, most significant
// first), which is exactly the model's `BitVec 128` value.  Byte buffers
// (for lxvw4x/stxvw4x) are printed as hex strings in address order.
//
//   powerpc64le-linux-gnu-gcc -O1 -static -mcpu=power8 ppc_insn_test.c -o ppc_insn_test
//   qemu-ppc64le ./ppc_insn_test > vectors.txt
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static uint64_t st = 0x0123456789abcdefULL;
static uint64_t rnd(void) {
  st ^= st << 13; st ^= st >> 7; st ^= st << 17;
  return st;
}

typedef struct { _Alignas(16) uint8_t b[16]; } vec;

static vec rv(void) {
  vec v;
  uint64_t x = rnd(), y = rnd();
  memcpy(v.b, &x, 8); memcpy(v.b + 8, &y, 8);
  return v;
}

static void pv(const vec *v) {
  printf(" ");
  for (int i = 15; i >= 0; i--) printf("%02x", v->b[i]);
}

static void pbytes(const uint8_t *p, int n) {
  printf(" ");
  for (int i = 0; i < n; i++) printf("%02x", p[i]);
}

#define LOAD3 "lvx 0,0,%1\n\tlvx 1,0,%2\n\tlvx 2,0,%3\n\t"
#define VOP3(NAME, INSN)                                                       \
  static void NAME(const vec *a, const vec *b, const vec *c, vec *d) {         \
    __asm__ volatile(LOAD3 INSN "\n\tstvx 3,0,%0"                             \
                     : : "r"(d->b), "r"(a->b), "r"(b->b), "r"(c->b)            \
                     : "v0", "v1", "v2", "v3", "memory");                      \
  }

VOP3(t_vadduwm, "vadduwm 3,0,1")
VOP3(t_vxor, "vxor 3,0,1")
VOP3(t_vor, "vor 3,0,1")
VOP3(t_vsel, "vsel 3,0,1,2")
VOP3(t_vperm, "vperm 3,0,1,2")
VOP3(t_vmrghw, "vmrghw 3,0,1")

#define SLD(N) VOP3(t_vsldoi_##N, "vsldoi 3,0,1," #N)
SLD(0) SLD(1) SLD(2) SLD(3) SLD(4) SLD(5) SLD(6) SLD(7)
SLD(8) SLD(9) SLD(10) SLD(11) SLD(12) SLD(13) SLD(14) SLD(15)
static void (*const t_vsldoi[16])(const vec *, const vec *, const vec *, vec *) = {
  t_vsldoi_0, t_vsldoi_1, t_vsldoi_2, t_vsldoi_3, t_vsldoi_4, t_vsldoi_5, t_vsldoi_6, t_vsldoi_7,
  t_vsldoi_8, t_vsldoi_9, t_vsldoi_10, t_vsldoi_11, t_vsldoi_12, t_vsldoi_13, t_vsldoi_14,
  t_vsldoi_15};

#define XXP(N) VOP3(t_xxpermdi_##N, "xxpermdi 35,32,33," #N)
XXP(0) XXP(1) XXP(2) XXP(3)
static void (*const t_xxpermdi[4])(const vec *, const vec *, const vec *, vec *) = {
  t_xxpermdi_0, t_xxpermdi_1, t_xxpermdi_2, t_xxpermdi_3};

#define SIG(ST, SIX) VOP3(t_sig_##ST##_##SIX, "vshasigmaw 3,0," #ST "," #SIX)
#define SIG16(ST) SIG(ST, 0) SIG(ST, 1) SIG(ST, 2) SIG(ST, 3) SIG(ST, 4) SIG(ST, 5) SIG(ST, 6) \
  SIG(ST, 7) SIG(ST, 8) SIG(ST, 9) SIG(ST, 10) SIG(ST, 11) SIG(ST, 12) SIG(ST, 13) SIG(ST, 14) \
  SIG(ST, 15)
SIG16(0) SIG16(1)
#define SIGP(ST) t_sig_##ST##_0, t_sig_##ST##_1, t_sig_##ST##_2, t_sig_##ST##_3, t_sig_##ST##_4, \
  t_sig_##ST##_5, t_sig_##ST##_6, t_sig_##ST##_7, t_sig_##ST##_8, t_sig_##ST##_9, t_sig_##ST##_10, \
  t_sig_##ST##_11, t_sig_##ST##_12, t_sig_##ST##_13, t_sig_##ST##_14, t_sig_##ST##_15
static void (*const t_sig[32])(const vec *, const vec *, const vec *, vec *) = {SIGP(0), SIGP(1)};

#define CMP(UI)                                                                \
  static void t_cmp_##UI(uint64_t x, uint32_t *cr) {                           \
    uint64_t c;                                                                \
    __asm__ volatile("cmpli 0,1,%1," #UI "\n\tmfcr %0" : "=r"(c) : "r"(x) : "cr0"); \
    *cr = (uint32_t)c;                                                         \
  }
CMP(0) CMP(1) CMP(64) CMP(65535)

int main(void) {
  static const char *three[] = {"vadduwm", "vxor", "vor", "vsel", "vperm", "vmrghw"};
  static void (*const f3[])(const vec *, const vec *, const vec *, vec *) = {
    t_vadduwm, t_vxor, t_vor, t_vsel, t_vperm, t_vmrghw};
  // the byte-swap mask used by the SHA-256 code, as loaded by lxvw4x
  vec mask;
  for (int i = 0; i < 16; i++) mask.b[i] = (uint8_t)(15 - i);  // not used directly below
  (void)mask;
  for (int i = 0; i < 1000; i++) {
    vec a = rv(), b = rv(), c = rv(), d;
    for (int k = 0; k < 6; k++) {
      f3[k](&a, &b, &c, &d);
      printf("%s", three[k]); pv(&a); pv(&b); pv(&c); pv(&d); printf("\n");
    }
    int sh = i % 16;
    t_vsldoi[sh](&a, &b, &c, &d);
    printf("vsldoi %d", sh); pv(&a); pv(&b); pv(&c); pv(&d); printf("\n");
    int dm = i % 4;
    t_xxpermdi[dm](&a, &b, &c, &d);
    printf("xxpermdi %d", dm); pv(&a); pv(&b); pv(&c); pv(&d); printf("\n");
    int sg = i % 32;
    t_sig[sg](&a, &b, &c, &d);
    printf("vshasigmaw %d %d", sg / 16, sg % 16); pv(&a); pv(&b); pv(&c); pv(&d); printf("\n");
    // lxvw4x from an unaligned address
    {
      uint8_t buf[32];
      for (int j = 0; j < 32; j++) buf[j] = (uint8_t)rnd();
      int off = (int)(rnd() % 16);
      __asm__ volatile("lxvw4x 35,0,%1\n\tstvx 3,0,%0" : : "r"(d.b), "r"(buf + off) : "v3", "memory");
      printf("lxvw4x"); pbytes(buf + off, 16); pv(&d); printf("\n");
    }
    // stxvw4x to an unaligned address
    {
      uint8_t buf[32];
      memset(buf, 0, sizeof buf);
      int off = (int)(rnd() % 16);
      __asm__ volatile("lvx 0,0,%1\n\tstxvw4x 32,0,%0" : : "r"(buf + off), "r"(a.b) : "v0", "memory");
      printf("stxvw4x"); pv(&a); pbytes(buf + off, 16); printf("\n");
    }
    // cmpli 0,1,RA,UI
    {
      uint64_t x = rnd();
      if (i % 4 == 0) x &= 0xff;
      if (i % 4 == 1) x &= 0x1ffff;
      if (i % 16 == 2) x = 0;
      if (i % 16 == 3) x = 1;
      if (i % 16 == 4) x = 64;
      if (i % 16 == 5) x = 65535;
      uint32_t cr;
      int ui;
      switch (i % 4) {
        case 0: t_cmp_0(x, &cr); ui = 0; break;
        case 1: t_cmp_1(x, &cr); ui = 1; break;
        case 2: t_cmp_64(x, &cr); ui = 64; break;
        default: t_cmp_65535(x, &cr); ui = 65535; break;
      }
      // CR0 is the most significant nibble of CR: LT GT EQ SO
      printf("cmpldi %d %016llx %d\n", ui, (unsigned long long)x, (int)((cr >> 29) & 7));
    }
    // addi RT,RA,SI and li RT,SI
    {
      uint64_t x = rnd(), r1, r2;
      __asm__ volatile("addi %0,%1,-1024" : "=r"(r1) : "b"(x));
      __asm__ volatile("addi %0,%1,32767" : "=r"(r2) : "b"(x));
      printf("addi %016llx %016llx %016llx\n", (unsigned long long)x, (unsigned long long)r1,
             (unsigned long long)r2);
    }
    // neg RT,RA
    {
      uint64_t x = rnd(), r;
      if (i % 8 == 0) x = 0;
      if (i % 8 == 1) x = 0x8000000000000000ULL;
      __asm__ volatile("neg %0,%1" : "=r"(r) : "r"(x));
      printf("neg %016llx %016llx\n", (unsigned long long)x, (unsigned long long)r);
    }
  }
  return 0;
}
