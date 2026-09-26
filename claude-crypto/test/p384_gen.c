// Generates test vectors for the P-384 ECDSA verifier with OpenSSL as the
// reference (run on a host that has OpenSSL):
//
//   cc -O2 p384_gen.c -lcrypto -o p384_gen && ./p384_gen > p384_vectors.txt
//
// Each line is `<pubkey x||y> <digest> <sig r||s> <expected 0/1>` (hex,
// big-endian).  The expected result is OpenSSL's: the public key is accepted
// iff EC_KEY_set_public_key_affine_coordinates accepts it (on the curve, both
// coordinates < p), and the signature iff ECDSA_do_verify returns 1.
#define OPENSSL_SUPPRESS_DEPRECATED
#include <openssl/bn.h>
#include <openssl/ec.h>
#include <openssl/ecdsa.h>
#include <openssl/obj_mac.h>
#include <openssl/rand.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static const EC_GROUP *g;
static BIGNUM *n, *p;
static BN_CTX *ctx;
static int count, nvalid;

static int ossl_verify(const uint8_t pub[96], const uint8_t dig[48], const uint8_t sig[96]) {
  EC_KEY *k = EC_KEY_new_by_curve_name(NID_secp384r1);
  BIGNUM *x = BN_bin2bn(pub, 48, NULL), *y = BN_bin2bn(pub + 48, 48, NULL);
  int ok = 0;
  if (EC_KEY_set_public_key_affine_coordinates(k, x, y) == 1) {
    ECDSA_SIG *s = ECDSA_SIG_new();
    ECDSA_SIG_set0(s, BN_bin2bn(sig, 48, NULL), BN_bin2bn(sig + 48, 48, NULL));
    ok = ECDSA_do_verify(dig, 48, s, k) == 1;
    ECDSA_SIG_free(s);
  }
  BN_free(x); BN_free(y); EC_KEY_free(k);
  return ok;
}

static void hex(const uint8_t *b, int n) { for (int i = 0; i < n; i++) printf("%02x", b[i]); }

static void emit(const uint8_t pub[96], const uint8_t dig[48], const uint8_t sig[96]) {
  int v = ossl_verify(pub, dig, sig);
  hex(pub, 96); printf(" "); hex(dig, 48); printf(" "); hex(sig, 96); printf(" %d\n", v);
  count++; nvalid += v;
}

static void bn48(const BIGNUM *b, uint8_t out[48]) { BN_bn2binpad(b, out, 48); }

/* The public key d·G. */
static void pub_of(const BIGNUM *d, uint8_t pub[96]) {
  EC_POINT *q = EC_POINT_new(g);
  BIGNUM *x = BN_new(), *y = BN_new();
  EC_POINT_mul(g, q, d, NULL, NULL, ctx);
  EC_POINT_get_affine_coordinates(g, q, x, y, ctx);
  bn48(x, pub); bn48(y, pub + 48);
  BN_free(x); BN_free(y); EC_POINT_free(q);
}

/* Sign `dig` with private key `d` (OpenSSL, random nonce). */
static void sign(const BIGNUM *d, const uint8_t dig[48], uint8_t sig[96]) {
  EC_KEY *k = EC_KEY_new_by_curve_name(NID_secp384r1);
  EC_KEY_set_private_key(k, d);
  EC_POINT *q = EC_POINT_new(g);
  EC_POINT_mul(g, q, d, NULL, NULL, ctx);
  EC_KEY_set_public_key(k, q);
  ECDSA_SIG *s = ECDSA_do_sign(dig, 48, k);
  bn48(ECDSA_SIG_get0_r(s), sig); bn48(ECDSA_SIG_get0_s(s), sig + 48);
  ECDSA_SIG_free(s); EC_POINT_free(q); EC_KEY_free(k);
}

/* A signature with prescribed u1 = e/s, u2 = r/s for the key d·G: with
   R = u1·G + u2·d·G, r = x(R) mod n, s = r/u2, e = u1·s.  (If u2 = 0 or r = 0
   this still produces a (then invalid) vector.) */
static void crafted(const BIGNUM *d, const BIGNUM *u1, const BIGNUM *u2) {
  uint8_t pub[96], dig[48], sig[96];
  pub_of(d, pub);
  BIGNUM *k = BN_new(), *r = BN_new(), *s = BN_new(), *e = BN_new(), *x = BN_new(), *t = BN_new();
  BN_mod_mul(t, u2, d, n, ctx);
  BN_mod_add(k, u1, t, n, ctx);                  // R = k·G
  EC_POINT *R = EC_POINT_new(g);
  EC_POINT_mul(g, R, k, NULL, NULL, ctx);
  if (EC_POINT_is_at_infinity(g, R)) BN_zero(r);
  else { EC_POINT_get_affine_coordinates(g, R, x, NULL, ctx); BN_nnmod(r, x, n, ctx); }
  if (BN_is_zero(u2)) BN_one(s);
  else { BN_mod_inverse(t, u2, n, ctx); BN_mod_mul(s, r, t, n, ctx); }
  if (BN_is_zero(s)) BN_one(s);
  BN_mod_mul(e, u1, s, n, ctx);
  bn48(e, dig); bn48(r, sig); bn48(s, sig + 48);
  emit(pub, dig, sig);
  BN_free(k); BN_free(r); BN_free(s); BN_free(e); BN_free(x); BN_free(t); EC_POINT_free(R);
}

int main(void) {
  ctx = BN_CTX_new();
  g = EC_GROUP_new_by_curve_name(NID_secp384r1);
  n = BN_new(); p = BN_new();
  EC_GROUP_get_order(g, n, ctx);
  EC_GROUP_get_curve(g, p, NULL, NULL, ctx);
  BIGNUM *d = BN_new(), *t = BN_new(), *u1 = BN_new(), *u2 = BN_new();
  uint8_t pub[96], dig[48], sig[96], p2[96], d2[48], s2[96];

  // 1. random keys: valid signatures and mutations
  for (int it = 0; it < 60; it++) {
    BN_rand_range(d, n); if (BN_is_zero(d)) BN_one(d);
    pub_of(d, pub);
    RAND_bytes(dig, 48);
    if (it % 10 == 1) memset(dig, 0xff, 48);             // e >= n
    if (it % 10 == 2) bn48(n, dig);                       // e = n
    if (it % 10 == 3) memset(dig, 0, 48);                 // e = 0 (u1 = 0)
    sign(d, dig, sig);
    for (int m = 0; m < 12; m++) {
      memcpy(p2, pub, 96); memcpy(d2, dig, 48); memcpy(s2, sig, 96);
      switch (m) {
        case 0: break;
        case 1: d2[it % 48] ^= 1 << (it % 8); break;
        case 2: s2[(it * 7) % 96] ^= 1 << (it % 8); break;
        case 3: p2[(it * 5) % 96] ^= 1 << (it % 8); break;
        case 4: memset(s2, 0, 48); break;                           // r = 0
        case 5: memset(s2 + 48, 0, 48); break;                      // s = 0
        case 6: bn48(n, s2); break;                                 // r = n
        case 7: bn48(n, s2 + 48); break;                            // s = n
        case 8: BN_bin2bn(s2 + 48, 48, t); BN_sub(t, n, t); bn48(t, s2 + 48); break;  // s -> n - s
        case 9: memset(p2, 0xff, 48); break;                        // x >= p
        case 10: BN_bin2bn(p2, 48, t); BN_add(t, t, p); if (BN_num_bytes(t) <= 48) bn48(t, p2); break;  // x + p
        case 11: BN_bin2bn(p2 + 48, 48, t); BN_sub(t, p, t); bn48(t, p2 + 48); break;  // -Q: invalid
      }
      emit(p2, d2, s2);
    }
  }

  // 2. pubkey = G (d = 1): the precomputation G + Q doubles
  BN_one(d); pub_of(d, pub);
  for (int it = 0; it < 6; it++) {
    RAND_bytes(dig, 48); sign(d, dig, sig); emit(pub, dig, sig);
    sig[95] ^= 1; emit(pub, dig, sig);
  }
  // 3. pubkey = -G (d = n - 1)
  BN_sub(d, n, BN_value_one()); pub_of(d, pub);
  for (int it = 0; it < 6; it++) { RAND_bytes(dig, 48); sign(d, dig, sig); emit(pub, dig, sig); }

  // 4. crafted scalars.  Q = 2G, u1 = 2, u2 = 1: after the first bit the
  //    accumulator is G, doubled to 2G, and then Q = 2G is added: the P = Q
  //    (doubling) case of the addition inside the ladder.  Valid signature.
  BN_set_word(d, 2); BN_set_word(u1, 2); BN_set_word(u2, 1); crafted(d, u1, u2);
  //    the same one bit lower down: u1 = 2^200 · 2, u2 = 2^200 (acc = 2^200 G after the top bits)
  BN_set_word(u1, 2); BN_lshift(u1, u1, 200); BN_one(u2); BN_lshift(u2, u2, 200); crafted(d, u1, u2);
  //    Q = G, u1 = 1, u2 = 1: G + Q doubles in the precomputation and in the ladder
  BN_one(d); BN_one(u1); BN_one(u2); crafted(d, u1, u2);
  //    Q = G, u1 = 1, u2 = n - 1: R = O (invalid)
  BN_one(d); BN_one(u1); BN_sub(u2, n, BN_value_one()); crafted(d, u1, u2);
  //    Q = 3G, u1 = n - 3, u2 = 1: R = O (invalid); the addition of G + Q hits P = -Q later
  BN_set_word(d, 3); BN_sub(u1, n, BN_value_one()); BN_sub_word(u1, 2); BN_one(u2); crafted(d, u1, u2);
  //    u1 = 0 (e = 0) and u2 = 1; and large random u1, u2
  BN_set_word(d, 12345); BN_zero(u1); BN_one(u2); crafted(d, u1, u2);
  for (int it = 0; it < 6; it++) {
    BN_rand_range(d, n); BN_rand_range(u1, n); BN_rand_range(u2, n);
    if (it == 0) { BN_sub(u1, n, BN_value_one()); BN_sub(u2, n, BN_value_one()); }
    crafted(d, u1, u2);
  }

  // 5. signature edge values with a random key
  BN_rand_range(d, n); pub_of(d, pub); RAND_bytes(dig, 48); sign(d, dig, sig);
  {
    const char *rs[] = {"1", "2", "-1", "-2", "p-n-1", "p-n", "p-n+1"};
    for (int i = 0; i < 7; i++) for (int j = 0; j < 3; j++) {
      memcpy(s2, sig, 96);
      BIGNUM *v = BN_new();
      if (!strcmp(rs[i], "1")) BN_one(v);
      else if (!strcmp(rs[i], "2")) BN_set_word(v, 2);
      else if (!strcmp(rs[i], "-1")) BN_sub(v, n, BN_value_one());
      else if (!strcmp(rs[i], "-2")) { BN_sub(v, n, BN_value_one()); BN_sub_word(v, 1); }
      else { BN_sub(v, p, n); if (!strcmp(rs[i], "p-n-1")) BN_sub_word(v, 1); if (!strcmp(rs[i], "p-n+1")) BN_add_word(v, 1); }
      if (j == 0 || j == 2) bn48(v, s2);          // r
      if (j == 1 || j == 2) bn48(v, s2 + 48);     // s
      emit(pub, dig, s2);
      BN_free(v);
    }
  }

  // 6. invalid public keys
  memset(p2, 0, 96); emit(p2, dig, sig);                          // (0, 0)
  BN_one(d); pub_of(d, p2); p2[95] ^= 1; emit(p2, dig, sig);      // (Gx, Gy ^ 1)
  pub_of(d, p2); bn48(p, p2 + 48); emit(p2, dig, sig);            // y = p
  pub_of(d, p2); memset(p2 + 48, 0xff, 48); emit(p2, dig, sig);   // y >= p
  pub_of(d, p2); BN_bin2bn(p2 + 48, 48, t); BN_add(t, t, p);      // (Gx, Gy + p) if it fits
  if (BN_num_bytes(t) <= 48) { bn48(t, p2 + 48); emit(p2, dig, sig); }
  for (int it = 0; it < 4; it++) { RAND_bytes(p2, 96); emit(p2, dig, sig); }  // random (off curve)

  fprintf(stderr, "%d vectors, %d valid\n", count, nvalid);
  return 0;
}
