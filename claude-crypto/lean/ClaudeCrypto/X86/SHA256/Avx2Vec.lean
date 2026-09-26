import ClaudeCrypto.X86.VecLemmas
import ClaudeCrypto.X86.SHA256.Avx2

/-! # Vector lemmas specific to the AVX2 SHA-256 message schedule -/

namespace CC.X86.SHA256Avx2

open BitVec CC.X86 CC.Spec.SHA256

theorem rotr_shifts (x : BitVec 32) (n : Nat) (hn : 0 < n) (hn2 : n < 32) :
    x >>> n ^^^ x <<< (32 - n) = x.rotateRight n := by
  apply eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_xor, getLsbD_ushiftRight, getLsbD_shiftLeft, getLsbD_rotateRight, hi, decide_true,
    Bool.true_and, Nat.mod_eq_of_lt hn2]
  by_cases h : i < 32 - n
  · simp only [h, ite_true, decide_true, Bool.not_true, Bool.false_and, Bool.xor_false]
  · simp only [h, ite_false, getLsbD_of_ge x (n + i) (by omega), decide_false, Bool.not_false,
      Bool.true_and, Bool.false_xor]

/-- σ₀ as computed by the vector code (shifts and xors). -/
theorem sigma0_shifts (x : BitVec 32) :
    x >>> 7 ^^^ x <<< 25 ^^^ x >>> 18 ^^^ x <<< 14 ^^^ x >>> 3 = sigma0 x := by
  have r7 : x >>> 7 ^^^ x <<< 25 = x.rotateRight 7 := rotr_shifts x 7 (by decide) (by decide)
  have r18 : x >>> 18 ^^^ x <<< 14 = x.rotateRight 18 := rotr_shifts x 18 (by decide) (by decide)
  rw [sigma0, ROTR, ROTR, SHR, ← r7, ← r18]
  simp only [BitVec.xor_assoc]

/-- The low dword of a duplicated dword shifted right is a rotation. -/
theorem lane_dup_shift (w : BitVec 32) (n : Nat) (hn : 0 < n) (hn2 : n < 32) :
    lane 32 ((w ++ w : BitVec 64) >>> n) 0 = w.rotateRight n := by
  apply eq_of_getLsbD_eq; intro i hi
  simp only [lane, getLsbD_extractLsb', getLsbD_ushiftRight, getLsbD_append, getLsbD_rotateRight, hi,
    decide_true, Bool.true_and, Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt hn2]
  by_cases h : i < 32 - n
  · simp only [show n + i < 32 by omega, h, ite_true]
  · simp only [show ¬ n + i < 32 by omega, h, ite_false]; congr 1; omega

theorem sigma1_shifts (w : BitVec 32) :
    w >>> 10 ^^^ lane 32 ((w ++ w : BitVec 64) >>> 17) 0 ^^^ lane 32 ((w ++ w : BitVec 64) >>> 19) 0 =
      sigma1 w := by
  rw [lane_dup_shift w 17 (by decide) (by decide), lane_dup_shift w 19 (by decide) (by decide),
    sigma1, ROTR, ROTR, SHR]
  rw [BitVec.xor_comm (w >>> 10), BitVec.xor_assoc, BitVec.xor_comm (w >>> 10), ← BitVec.xor_assoc]

/-- A 64-bit lane is the concatenation of two 32-bit lanes. -/
theorem lane64_eq (x : BitVec 256) (q : Nat) (hq : q < 4) :
    lane 64 x q = lane 32 x (2 * q + 1) ++ lane 32 x (2 * q) := by
  apply eq_of_getLsbD_eq; intro k hk
  simp only [lane, getLsbD_extractLsb', getLsbD_append, hk, decide_true, Bool.true_and]
  by_cases h : k < 32
  · simp only [h, ite_true, decide_true, Bool.true_and]; congr 1; omega
  · simp only [h, ite_false, show k - 32 < 32 by omega, decide_true, Bool.true_and]; congr 1; omega

/-! ## Byte shuffles with the constant masks -/

/-- A constant vector given by its 32 bytes (byte 0 least significant). -/
def maskV (bytes : List (BitVec 8)) : BitVec 256 := lanes 32 fun i => bytes[i]!

theorem lane32_lanes8_128 (G : Nat → BitVec 8) (j : Nat) (hj : j < 4) :
    lane 32 (lanes 16 G : BitVec 128) j = G (4 * j + 3) ++ G (4 * j + 2) ++ G (4 * j + 1) ++ G (4 * j) := by
  apply eq_of_getLsbD_eq; intro k hk
  simp only [lane, getLsbD_extractLsb', getLsbD_lanes, getLsbD_append, hk, decide_true, Bool.true_and]
  have : 32 * j + k < 8 * 16 := by omega
  simp only [this, decide_true, Bool.true_and]
  by_cases a : k < 8
  · simp only [a, ite_true, decide_true, Bool.true_and]
    rw [show (32 * j + k) / 8 = 4 * j by omega, show (32 * j + k) % 8 = k by omega]
  by_cases b : k < 16
  · simp only [a, b, ite_true, ite_false, show k - 8 < 8 by omega, decide_true, Bool.true_and]
    rw [show (32 * j + k) / 8 = 4 * j + 1 by omega, show (32 * j + k) % 8 = k - 8 by omega]
  by_cases c : k < 24
  · simp only [a, b, c, ite_true, ite_false, show k - 8 - 8 < 8 by omega, show ¬ k - 8 < 8 by omega,
      decide_true, Bool.true_and]
    rw [show (32 * j + k) / 8 = 4 * j + 2 by omega, show (32 * j + k) % 8 = k - 8 - 8 by omega]
  · simp only [a, b, c, ite_false, show ¬ k - 8 < 8 by omega, show ¬ k - 8 - 8 < 8 by omega,
      show k - 8 - 8 - 8 < 8 by omega, decide_true, Bool.true_and]
    rw [show (32 * j + k) / 8 = 4 * j + 3 by omega, show (32 * j + k) % 8 = k - 8 - 8 - 8 by omega]

theorem lane8_maskV (bytes : List (BitVec 8)) (L b : Nat) (hL : L < 2) (hb : b < 16) :
    lane 8 (lane 128 (maskV bytes) L) b = bytes[16 * L + b]! := by
  rw [lane8_lane128 _ _ _ hL hb, maskV, lane_lanes 32 _ _ (by omega)]

/-- Evaluate one 32-bit lane of `vpshufb` with a constant mask. -/
theorem lane_vpshufb_mask (x : BitVec 256) (bytes : List (BitVec 8)) (i : Nat) (hi : i < 8) :
    lane 32 (vpshufbV x (maskV bytes)) i =
      let sel (b : Nat) : BitVec 8 :=
        let c := bytes[16 * (i / 4) + b]!
        if c.msb then 0 else lane 8 x (16 * (i / 4) + c.toNat % 16)
      sel (4 * (i % 4) + 3) ++ sel (4 * (i % 4) + 2) ++ sel (4 * (i % 4) + 1) ++ sel (4 * (i % 4)) := by
  rw [vpshufbV, lane32_lanes128 _ i hi, pshufb128, lane32_lanes8_128 _ _ (Nat.mod_lt _ (by decide))]
  simp only [lane8_maskV _ _ _ (show i / 4 < 2 by omega) (show 4 * (i % 4) + 3 < 16 by omega),
    lane8_maskV _ _ _ (show i / 4 < 2 by omega) (show 4 * (i % 4) + 2 < 16 by omega),
    lane8_maskV _ _ _ (show i / 4 < 2 by omega) (show 4 * (i % 4) + 1 < 16 by omega),
    lane8_maskV _ _ _ (show i / 4 < 2 by omega) (show 4 * (i % 4) < 16 by omega)]
  have h : ∀ c : BitVec 8, lane 8 (lane 128 x (i / 4)) (c.toNat % 16) = lane 8 x (16 * (i / 4) + c.toNat % 16) :=
    fun c => lane8_lane128 _ _ _ (by omega) (Nat.mod_lt _ (by decide))
  simp only [h]

theorem bswap32_concat (a b c d : BitVec 8) : bswap32 (a ++ b ++ c ++ d) = d ++ c ++ b ++ a := by
  apply eq_of_getLsbD_eq; intro k hk
  simp only [bswap32, getLsbD_append, getLsbD_extractLsb']
  interval_cases k <;> simp

theorem lane_bswap (x : BitVec 256) (i : Nat) (hi : i < 8) :
    lane 32 (vpshufbV x (maskV bswapMask)) i = bswap32 (lane 32 x i) := by
  rw [lane_vpshufb_mask _ _ _ hi, lane32_bytes x i hi, bswap32_concat]
  interval_cases i <;> simp (config := { decide := true }) [bswapMask]

theorem zero_concat8 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 32) = 0 := by decide

theorem lane_shuf00BA (x : BitVec 256) (i : Nat) (hi : i < 8) :
    lane 32 (vpshufbV x (maskV shuf00BA)) i =
      if i % 4 = 0 then lane 32 x i else if i % 4 = 1 then lane 32 x (i + 1) else 0 := by
  rw [lane_vpshufb_mask _ _ _ hi]
  interval_cases i <;> simp (config := { decide := true }) [shuf00BA, lane32_bytes, zero_concat8]

theorem lane_shufDC00 (x : BitVec 256) (i : Nat) (hi : i < 8) :
    lane 32 (vpshufbV x (maskV shufDC00)) i =
      if i % 4 = 2 then lane 32 x (i - 2) else if i % 4 = 3 then lane 32 x (i - 1) else 0 := by
  rw [lane_vpshufb_mask _ _ _ hi]
  interval_cases i <;> simp (config := { decide := true }) [shufDC00, lane32_bytes, zero_concat8]

end CC.X86.SHA256Avx2
