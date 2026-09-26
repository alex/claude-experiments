import Mathlib.Tactic

/-! # Montgomery multiplication over ℕ (word size `2^64`) -/

namespace CC.Limb.Mont

/-- One Montgomery round's quotient digit. -/
def qDigit (mp U : Nat) : Nat := U % 2 ^ 64 * mp % 2 ^ 64

theorem qDigit_lt (mp U : Nat) : qDigit mp U < 2 ^ 64 := Nat.mod_lt _ (by positivity)

/-- `U + q N` is divisible by the word size when `mp · N ≡ -1`. -/
theorem round_dvd (N mp U : Nat) (hmp : (mp * N + 1) % 2 ^ 64 = 0) :
    (U + qDigit mp U * N) % 2 ^ 64 = 0 := by
  rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff] at *
  unfold qDigit
  push_cast [ZMod.natCast_mod] at *
  linear_combination (U : ZMod (2 ^ 64)) * hmp

theorem round_bound (N T A b q : Nat) (hT : T < 2 * N) (hA : A < N) (hb : b < 2 ^ 64) (hq : q < 2 ^ 64) :
    (T + A * b + q * N) / 2 ^ 64 < 2 * N := by
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  zify at *
  nlinarith [mul_le_mul_of_nonneg_right (show (A : ℤ) ≤ N - 1 by omega) (show (0 : ℤ) ≤ b by positivity),
    mul_le_mul_of_nonneg_left (show (b : ℤ) ≤ 2 ^ 64 - 1 by omega) (show (0 : ℤ) ≤ N - 1 by omega),
    mul_le_mul_of_nonneg_right (show (q : ℤ) ≤ 2 ^ 64 - 1 by omega) (show (0 : ℤ) ≤ N by positivity)]

end CC.Limb.Mont
