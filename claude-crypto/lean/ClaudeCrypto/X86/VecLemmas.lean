import ClaudeCrypto.X86.Basic

/-!
# Lane-wise characterizations of the AVX2 instruction semantics

Proof support (not part of the TCB): each lemma computes one 32-bit lane of
an instruction's result in terms of lanes of its inputs.
-/

namespace CC.X86

open BitVec

theorem lane32_lanes128 (G : Nat → BitVec 128) (i : Nat) (hi : i < 8) :
    lane 32 (lanes 2 G : BitVec 256) i = lane 32 (G (i / 4)) (i % 4) := by
  apply eq_of_getLsbD_eq; intro j hj
  simp only [lane, getLsbD_extractLsb', getLsbD_lanes, hj, decide_true, Bool.true_and]
  have h1 : 32 * i + j < 128 * 2 := by omega
  have h2 : (32 * i + j) / 128 = i / 4 := by omega
  have h3 : (32 * i + j) % 128 = 32 * (i % 4) + j := by omega
  simp [h1, h2, h3]

theorem lane32_lanes64 (G : Nat → BitVec 64) (i : Nat) (hi : i < 8) :
    lane 32 (lanes 4 G : BitVec 256) i = lane 32 (G (i / 2)) (i % 2) := by
  apply eq_of_getLsbD_eq; intro j hj
  simp only [lane, getLsbD_extractLsb', getLsbD_lanes, hj, decide_true, Bool.true_and]
  have h1 : 32 * i + j < 64 * 4 := by omega
  have h2 : (32 * i + j) / 64 = i / 2 := by omega
  have h3 : (32 * i + j) % 64 = 32 * (i % 2) + j := by omega
  simp [h1, h2, h3]

theorem lane32_lanes32 (G : Nat → BitVec 32) (i : Nat) (hi : i < 8) :
    lane 32 (lanes 8 G : BitVec 256) i = G i := lane_lanes 8 G i hi

theorem lane32_lanes32_128 (G : Nat → BitVec 32) (i : Nat) (hi : i < 4) :
    lane 32 (lanes 4 G : BitVec 128) i = G i := lane_lanes 4 G i hi

theorem lane32_lane128 (x : BitVec 256) (L j : Nat) (hL : L < 2) (hj : j < 4) :
    lane 32 (lane 128 x L) j = lane 32 x (4 * L + j) := by
  apply eq_of_getLsbD_eq; intro k hk
  simp only [lane, getLsbD_extractLsb', hk, decide_true, Bool.true_and]
  have : 32 * j + k < 128 := by omega
  simp only [this, decide_true, Bool.true_and]
  congr 1; omega

theorem lane32_lane64 (x : BitVec 256) (q r : Nat) (hq : q < 4) (hr : r < 2) :
    lane 32 (lane 64 x q) r = lane 32 x (2 * q + r) := by
  apply eq_of_getLsbD_eq; intro k hk
  simp only [lane, getLsbD_extractLsb', hk, decide_true, Bool.true_and]
  have : 32 * r + k < 64 := by omega
  simp only [this, decide_true, Bool.true_and]
  congr 1; omega

theorem lane8_lane128 (x : BitVec 256) (L b : Nat) (hL : L < 2) (hb : b < 16) :
    lane 8 (lane 128 x L) b = lane 8 x (16 * L + b) := by
  apply eq_of_getLsbD_eq; intro k hk
  simp only [lane, getLsbD_extractLsb', hk, decide_true, Bool.true_and]
  have : 8 * b + k < 128 := by omega
  simp only [this, decide_true, Bool.true_and]
  congr 1; omega

/-- A 32-bit lane is the concatenation of its four bytes. -/
theorem lane32_bytes (x : BitVec 256) (i : Nat) (hi : i < 8) :
    lane 32 x i = lane 8 x (4 * i + 3) ++ lane 8 x (4 * i + 2) ++ lane 8 x (4 * i + 1) ++ lane 8 x (4 * i) := by
  apply eq_of_getLsbD_eq; intro k hk
  simp only [lane, getLsbD_extractLsb', getLsbD_append, hk, decide_true, Bool.true_and]
  have : k < 32 := hk
  by_cases a : k < 8
  · simp only [a, ite_true, decide_true, Bool.true_and]; congr 1; omega
  by_cases b : k < 16
  · simp only [a, b, ite_true, ite_false, show k - 8 < 8 by omega, decide_true, Bool.true_and]; congr 1; omega
  by_cases c : k < 24
  · simp only [a, b, c, ite_true, ite_false, show k - 8 - 8 < 8 by omega, show ¬ k - 8 < 8 by omega,
      decide_true, Bool.true_and]
    congr 1; omega
  · simp only [a, b, c, ite_false, show ¬ k - 8 < 8 by omega, show ¬ k - 8 - 8 < 8 by omega,
      show k - 8 - 8 - 8 < 8 by omega, decide_true, Bool.true_and]
    congr 1; omega

theorem lane8_lanes8_128 (G : Nat → BitVec 8) (b : Nat) (hb : b < 16) :
    lane 8 (lanes 16 G : BitVec 128) b = G b := lane_lanes 16 G b hb

/-! ## Per-instruction lane equations -/

theorem lane_vpaddd (x y : BitVec 256) (i : Nat) (hi : i < 8) :
    lane 32 (vpadddV x y) i = lane 32 x i + lane 32 y i := lane_lanes 8 _ i hi

theorem lane_vpxor (x y : BitVec 256) (i : Nat) :
    lane 32 (x ^^^ y) i = lane 32 x i ^^^ lane 32 y i := by
  apply eq_of_getLsbD_eq; intro k hk
  simp [lane, getLsbD_extractLsb', hk]

theorem lane_vpsrld (x : BitVec 256) (n i : Nat) (hn : n ≤ 31) (hi : i < 8) :
    lane 32 (vpsrldV x n) i = lane 32 x i >>> n := by
  rw [vpsrldV, lane32_lanes32 _ i hi, if_neg (by omega)]

theorem lane_vpslld (x : BitVec 256) (n i : Nat) (hn : n ≤ 31) (hi : i < 8) :
    lane 32 (vpslldV x n) i = lane 32 x i <<< n := by
  rw [vpslldV, lane32_lanes32 _ i hi, if_neg (by omega)]

theorem lane_vpsrlq (x : BitVec 256) (n i : Nat) (hn : n ≤ 63) (hi : i < 8) :
    lane 32 (vpsrlqV x n) i = lane 32 (lane 64 x (i / 2) >>> n) (i % 2) := by
  rw [vpsrlqV, lane32_lanes64 _ i hi, if_neg (by omega)]

theorem lane_vpshufd (x : BitVec 256) (imm i : Nat) (hi : i < 8) :
    lane 32 (vpshufdV x imm) i = lane 32 x (4 * (i / 4) + (imm / 4 ^ (i % 4)) % 4) := by
  rw [vpshufdV, lane32_lanes128 _ i hi, pshufd128, lane32_lanes32_128 _ _ (Nat.mod_lt _ (by decide)),
    lane32_lane128 _ _ _ (by omega) (Nat.mod_lt _ (by decide))]

theorem lane_vpalignr4 (x y : BitVec 256) (i : Nat) (hi : i < 8) :
    lane 32 (vpalignrV x y 4) i = if i % 4 < 3 then lane 32 y (i + 1) else lane 32 x (i - 3) := by
  rw [vpalignrV, lane32_lanes128 _ i hi, palignr128]
  apply eq_of_getLsbD_eq; intro k hk
  have hL : i / 4 < 2 := by omega
  simp only [lane, getLsbD_extractLsb', getLsbD_setWidth, getLsbD_ushiftRight, getLsbD_append, hk,
    decide_true, Bool.true_and]
  have h128 : 32 * (i % 4) + k < 128 := by omega
  simp only [h128, decide_true, Bool.true_and]
  by_cases h : i % 4 < 3
  · have c : 8 * 4 + (32 * (i % 4) + k) < 128 := by omega
    simp only [c, ite_true, decide_true, Bool.true_and, h, getLsbD_extractLsb', hk]
    rw [show 128 * (i / 4) + (8 * 4 + (32 * (i % 4) + k)) = 32 * (i + 1) + k by omega]
  · have c : ¬ 8 * 4 + (32 * (i % 4) + k) < 128 := by omega
    have c2 : 8 * 4 + (32 * (i % 4) + k) - 128 < 128 := by omega
    simp only [c, c2, ite_false, decide_true, Bool.true_and, h, getLsbD_extractLsb', hk]
    rw [show 128 * (i / 4) + (8 * 4 + (32 * (i % 4) + k) - 128) = 32 * (i - 3) + k by omega]

end CC.X86
