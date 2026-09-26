// Tests a SHA-256 block function against OpenSSL, and benchmarks it.
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifdef NO_OPENSSL
/* A straightforward portable reference SHA-256 (FIPS 180-4), used when OpenSSL
 * is not available for the target (e.g. when cross-compiling for AArch64 and
 * running under qemu). */
static const uint32_t RK[64] = {
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};
#define ROR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))
static void ref_block(uint32_t H[8], const uint8_t *p) {
  uint32_t W[64], v[8];
  for (int t = 0; t < 16; t++)
    W[t] = (uint32_t)p[4*t] << 24 | (uint32_t)p[4*t+1] << 16 | (uint32_t)p[4*t+2] << 8 | p[4*t+3];
  for (int t = 16; t < 64; t++) {
    uint32_t s0 = ROR(W[t-15], 7) ^ ROR(W[t-15], 18) ^ (W[t-15] >> 3);
    uint32_t s1 = ROR(W[t-2], 17) ^ ROR(W[t-2], 19) ^ (W[t-2] >> 10);
    W[t] = W[t-16] + s0 + W[t-7] + s1;
  }
  memcpy(v, H, sizeof v);
  for (int t = 0; t < 64; t++) {
    uint32_t e = v[4], a = v[0];
    uint32_t t1 = v[7] + (ROR(e, 6) ^ ROR(e, 11) ^ ROR(e, 25)) + ((e & v[5]) ^ (~e & v[6])) + RK[t] + W[t];
    uint32_t t2 = (ROR(a, 2) ^ ROR(a, 13) ^ ROR(a, 22)) + ((a & v[1]) ^ (a & v[2]) ^ (v[1] & v[2]));
    memmove(v + 1, v, 7 * sizeof(uint32_t));
    v[4] += t1; v[0] = t1 + t2;
  }
  for (int i = 0; i < 8; i++) H[i] += v[i];
}
static uint8_t *SHA256(const uint8_t *msg, size_t len, uint8_t out[32]) {
  uint32_t H[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                   0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
  size_t full = len / 64;
  for (size_t i = 0; i < full; i++) ref_block(H, msg + 64 * i);
  uint8_t tail[128] = {0};
  size_t rem = len - 64 * full;
  memcpy(tail, msg + 64 * full, rem);
  tail[rem] = 0x80;
  size_t tl = rem < 56 ? 64 : 128;
  uint64_t bits = (uint64_t)len * 8;
  for (int i = 0; i < 8; i++) tail[tl - 1 - i] = (uint8_t)(bits >> (8 * i));
  for (size_t i = 0; i < tl / 64; i++) ref_block(H, tail + 64 * i);
  for (int i = 0; i < 8; i++) {
    out[4*i] = H[i] >> 24; out[4*i+1] = H[i] >> 16; out[4*i+2] = H[i] >> 8; out[4*i+3] = H[i];
  }
  return out;
}
#else
#include <openssl/sha.h>
#endif

void SHA_BLOCKS(uint32_t H[8], const uint8_t *data, size_t nblocks);

static void sha256(const uint8_t *msg, size_t len, uint8_t out[32]) {
  uint32_t H[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                   0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
  size_t full = len / 64;
  SHA_BLOCKS(H, msg, full);
  uint8_t tail[128] = {0};
  size_t rem = len - 64 * full;
  memcpy(tail, msg + 64 * full, rem);
  tail[rem] = 0x80;
  size_t tl = rem < 56 ? 64 : 128;
  uint64_t bits = (uint64_t)len * 8;
  for (int i = 0; i < 8; i++) tail[tl - 1 - i] = (uint8_t)(bits >> (8 * i));
  SHA_BLOCKS(H, tail, tl / 64);
  for (int i = 0; i < 8; i++) {
    out[4*i] = H[i] >> 24; out[4*i+1] = H[i] >> 16; out[4*i+2] = H[i] >> 8; out[4*i+3] = H[i];
  }
}

static double now(void) {
  struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int known_answers(void) {
  static const char *msgs[] = {"", "abc",
    "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"};
  static const char *hex[] = {
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"};
  for (int i = 0; i < 3; i++) {
    uint8_t out[32], ref[32];
    sha256((const uint8_t *)msgs[i], strlen(msgs[i]), out);
    SHA256((const uint8_t *)msgs[i], strlen(msgs[i]), ref);
    for (int j = 0; j < 32; j++) {
      unsigned x;
      sscanf(hex[i] + 2 * j, "%2x", &x);
      if (out[j] != x || ref[j] != x) { printf("KAT %d FAILED\n", i); return 1; }
    }
  }
  printf("known answers OK\n");
  return 0;
}

int main(int argc, char **argv) {
  if (known_answers()) return 1;
  srand(1234);
  uint8_t buf[4096];
  for (int iter = 0; iter < 20000; iter++) {
    size_t len = rand() % (iter < 1000 ? 300 : 4096);
    for (size_t i = 0; i < len; i++) buf[i] = rand();
    uint8_t a[32], b[32];
    sha256(buf, len, a);
    SHA256(buf, len, b);
    if (memcmp(a, b, 32)) { printf("MISMATCH len=%zu\n", len); return 1; }
  }
  printf("correctness: 20000 random messages OK\n");
  if (argc > 1) {
    size_t n = 16384; uint8_t *big = malloc(n); memset(big, 7, n);
    uint32_t H[8] = {0};
    int reps = 20000;
    double best = 1e9, bestO = 1e9;
    for (int trial = 0; trial < 5; trial++) {
      double t0 = now();
      for (int r = 0; r < reps; r++) SHA_BLOCKS(H, big, n / 64);
      double t1 = now();
      uint8_t o[32];
      for (int r = 0; r < reps; r++) SHA256(big, n, o);
      double t2 = now();
      if (t1 - t0 < best) best = t1 - t0;
      if (t2 - t1 < bestO) bestO = t2 - t1;
    }
    printf("claude-crypto: %.1f MB/s\nopenssl:       %.1f MB/s\n",
           reps * n / best / 1e6, reps * n / bestO / 1e6);
  }
  return 0;
}
