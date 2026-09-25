// Tests a SHA-256 block function against OpenSSL, and benchmarks it.
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <openssl/sha.h>

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

int main(int argc, char **argv) {
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
