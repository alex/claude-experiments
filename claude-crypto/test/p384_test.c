// Tests the generated P-384 ECDSA verifier (asm/*/p384_verify.S).
//
//   p384_test <vectors.txt> [iters]
//
// 1. checks every vector of the file (see p384_gen.c; the expected results
//    come from OpenSSL), including the special cases of the point arithmetic;
// 2. unless built with -DNO_OPENSSL: a differential test against OpenSSL on
//    `iters` fresh random keys, each with 8 mutations of the signature,
//    digest and public key (default 200);
// 3. a benchmark (and, with OpenSSL, OpenSSL's speed on the same input).
//
// x86-64:  cc -O2 p384_test.c ../asm/x86_64/p384_verify.S -lcrypto -o p384_test
// aarch64: aarch64-linux-gnu-gcc -O2 -static -DNO_OPENSSL -DP384_VERIFY=cc_p384_verify_aarch64
//            p384_test.c ../asm/aarch64/p384_verify.S -o p384_test   (one line)
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifndef P384_VERIFY
#define P384_VERIFY cc_p384_verify_x86_bmi2
#endif
/* Returns 1 (valid) or 0 (invalid) in the full return register. */
uint64_t P384_VERIFY(const uint8_t pub[96], const uint8_t dig[48], const uint8_t sig[96]);

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + t.tv_nsec * 1e-9;
}

static int unhex(const char *s, uint8_t *out, int n) {
  for (int i = 0; i < n; i++) {
    unsigned v;
    if (sscanf(s + 2 * i, "%2x", &v) != 1) return 0;
    out[i] = (uint8_t)v;
  }
  return 1;
}

#ifndef NO_OPENSSL
#define OPENSSL_SUPPRESS_DEPRECATED
#include <openssl/bn.h>
#include <openssl/ec.h>
#include <openssl/ecdsa.h>
#include <openssl/obj_mac.h>
#include <openssl/rand.h>

static int ossl_verify_key(EC_KEY *k, const uint8_t dig[48], const uint8_t sig[96]) {
  ECDSA_SIG *s = ECDSA_SIG_new();
  ECDSA_SIG_set0(s, BN_bin2bn(sig, 48, NULL), BN_bin2bn(sig + 48, 48, NULL));
  int v = ECDSA_do_verify(dig, 48, s, k);
  ECDSA_SIG_free(s);
  return v == 1;
}

static int ossl_verify(const uint8_t pub[96], const uint8_t dig[48], const uint8_t sig[96]) {
  EC_KEY *k = EC_KEY_new_by_curve_name(NID_secp384r1);
  BIGNUM *x = BN_bin2bn(pub, 48, NULL), *y = BN_bin2bn(pub + 48, 48, NULL);
  int ok = EC_KEY_set_public_key_affine_coordinates(k, x, y) == 1 && ossl_verify_key(k, dig, sig);
  BN_free(x); BN_free(y); EC_KEY_free(k);
  return ok;
}

/* Random differential test with mutations. */
static int differential(int iters) {
  const EC_GROUP *g = EC_GROUP_new_by_curve_name(NID_secp384r1);
  BIGNUM *order = BN_new();
  EC_GROUP_get_order(g, order, NULL);
  int fails = 0, valid = 0, total = 0;
  for (int it = 0; it < iters; it++) {
    EC_KEY *k = EC_KEY_new_by_curve_name(NID_secp384r1);
    EC_KEY_generate_key(k);
    uint8_t pt[97], pub[96], dig[48], sig[96];
    EC_POINT_point2oct(g, EC_KEY_get0_public_key(k), POINT_CONVERSION_UNCOMPRESSED, pt, 97, NULL);
    memcpy(pub, pt + 1, 96);
    RAND_bytes(dig, 48);
    if (it % 7 == 0) memset(dig, 0xff, 48);  // e >= n
    ECDSA_SIG *s = ECDSA_do_sign(dig, 48, k);
    BN_bn2binpad(ECDSA_SIG_get0_r(s), sig, 48);
    BN_bn2binpad(ECDSA_SIG_get0_s(s), sig + 48, 48);
    ECDSA_SIG_free(s);
    EC_KEY_free(k);
    for (int m = 0; m < 8; m++) {
      uint8_t p2[96], d2[48], s2[96];
      memcpy(p2, pub, 96); memcpy(d2, dig, 48); memcpy(s2, sig, 96);
      switch (m) {
        case 0: break;
        case 1: d2[it % 48] ^= 1 << (it % 8); break;
        case 2: s2[it % 96] ^= 1 << (it % 8); break;
        case 3: p2[it % 96] ^= 1 << (it % 8); break;
        case 4: memset(s2, 0, 48); break;              // r = 0
        case 5: BN_bn2binpad(order, s2 + 48, 48); break;  // s = n
        case 6: memset(p2, 0xff, 48); break;           // x >= p
        case 7: {                                      // s -> n - s
          BIGNUM *sb = BN_bin2bn(s2 + 48, 48, NULL);
          BN_sub(sb, order, sb); BN_bn2binpad(sb, s2 + 48, 48); BN_free(sb);
          break;
        }
      }
      int ours = P384_VERIFY(p2, d2, s2) == 1, theirs = ossl_verify(p2, d2, s2);
      total++; valid += theirs;
      if (ours != theirs) {
        fails++;
        if (fails < 10) printf("MISMATCH it=%d m=%d ours=%d openssl=%d\n", it, m, ours, theirs);
      }
    }
  }
  printf("differential vs OpenSSL: %d cases (%d valid), %d mismatches\n", total, valid, fails);
  BN_free(order);
  return fails;
}
#endif

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: %s vectors.txt [iters]\n", argv[0]); return 2; }
  int iters = argc > 2 ? atoi(argv[2]) : 200;
  FILE *f = fopen(argv[1], "r");
  if (!f) { perror(argv[1]); return 2; }
  static char line[1024];
  int total = 0, valid = 0, fails = 0, have_bench = 0;
  uint8_t bpub[96], bdig[48], bsig[96];
  while (fgets(line, sizeof line, f)) {
    uint8_t pub[96], dig[48], sig[96];
    int expect;
    if (strlen(line) < 2 * (96 + 48 + 96) + 4) continue;
    if (!unhex(line, pub, 96) || !unhex(line + 193, dig, 48) || !unhex(line + 290, sig, 96) ||
        sscanf(line + 483, "%d", &expect) != 1) {
      printf("bad line: %s", line); return 2;
    }
    uint64_t got = P384_VERIFY(pub, dig, sig);
    total++; valid += expect;
    if (got != (uint64_t)expect) {
      fails++;
      if (fails < 10) printf("MISMATCH vector %d: got %llu, expected %d\n", total, (unsigned long long)got, expect);
    }
    if (expect && !have_bench) { memcpy(bpub, pub, 96); memcpy(bdig, dig, 48); memcpy(bsig, sig, 96); have_bench = 1; }
  }
  fclose(f);
  printf("vectors: %d (%d valid), %d mismatches\n", total, valid, fails);
#ifndef NO_OPENSSL
  fails += differential(iters);
#endif
  if (have_bench) {
    int N = iters * 10;
    double t0 = now();
    uint64_t acc = 0;
    for (int i = 0; i < N; i++) acc += P384_VERIFY(bpub, bdig, bsig);
    double t1 = now();
    printf("claude-crypto: %.0f verify/s (%.1f us)%s\n", N / (t1 - t0), (t1 - t0) / N * 1e6,
           acc == (uint64_t)N ? "" : "  WRONG RESULT");
    if (acc != (uint64_t)N) fails++;
#ifndef NO_OPENSSL
    EC_KEY *k = EC_KEY_new_by_curve_name(NID_secp384r1);
    BIGNUM *x = BN_bin2bn(bpub, 48, NULL), *y = BN_bin2bn(bpub + 48, 48, NULL);
    EC_KEY_set_public_key_affine_coordinates(k, x, y);
    t0 = now();
    acc = 0;
    for (int i = 0; i < N; i++) acc += ossl_verify_key(k, bdig, bsig);
    t1 = now();
    printf("openssl:       %.0f verify/s (%.1f us)\n", N / (t1 - t0), (t1 - t0) / N * 1e6);
    BN_free(x); BN_free(y); EC_KEY_free(k);
#endif
  }
  return fails != 0;
}
