import ClaudeCrypto.Spec.P384Facts

/-!
# Montgomery arithmetic over `ℕ`

Generic facts (in the modulus `N` and the Montgomery radix `R`) for connecting
limb-level Montgomery multiplication / reduction to `ZMod N`:

* `redc_cast`: if `R ∣ T + m·N` then `(T + m·N) / R ≡ T·R⁻¹ (mod N)`;
* `redc_dvd`: the usual choice `m = (T·N') mod R` with `N·N' ≡ −1 (mod R)` makes
  `R ∣ T + m·N`;
* `redc_lt`: `T < N·R`, `m < R` ⟹ `(T + m·N) / R < 2N`;
* `condSub_eq_mod`: the final conditional subtraction computes `x mod N` for `x < 2N`;
* `redc_step_cast`: word-by-word (CIOS) steps compose;
* `mont_mul_cast`: Montgomery multiplication of Montgomery forms.

At the end, the coprimality facts for P-384's `p` and `n` with `2^64` and `2^384`.
-/

namespace CC.Spec.Montgomery

/-- The core REDC identity, multiplied out: `((T + m·N) / R) · R ≡ T (mod N)`. -/
theorem redc_mul_cast {N R : ℕ} (T m : ℕ) (h : R ∣ T + m * N) :
    (((T + m * N) / R : ℕ) : ZMod N) * (R : ZMod N) = T := by
  rw [← Nat.cast_mul, Nat.div_mul_cancel h, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
    mul_zero, add_zero]

/-- The REDC identity in `ZMod N`: `(T + m·N) / R = T · R⁻¹` when `R ∣ T + m·N` and `R` is
invertible mod `N`. -/
theorem redc_cast {N R : ℕ} (hR : Nat.Coprime R N) (T m : ℕ) (h : R ∣ T + m * N) :
    (((T + m * N) / R : ℕ) : ZMod N) = T * (R : ZMod N)⁻¹ := by
  rw [← redc_mul_cast T m h, mul_assoc, ZMod.coe_mul_inv_eq_one _ hR, mul_one]

/-- Divisibility for the standard choice of `m`: if `N·N' ≡ −1 (mod R)` (i.e.
`R ∣ N·N' + 1`) and `m ≡ T·N' (mod R)`, then `R ∣ T + m·N`. -/
theorem redc_dvd {N N' R : ℕ} (hN' : R ∣ N * N' + 1) (T m : ℕ) (hm : m % R = T * N' % R) :
    R ∣ T + m * N := by
  rw [← ZMod.natCast_eq_zero_iff] at hN' ⊢
  have hm' : (m : ZMod R) = T * N' := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']; exact hm
  push_cast at hN' ⊢
  rw [hm']
  linear_combination (T : ZMod R) * hN'

/-- `m = (T mod R)·N' mod R` also works (only the low limb of `T` is needed). -/
theorem redc_dvd' {N N' R : ℕ} (hN' : R ∣ N * N' + 1) (T : ℕ) :
    R ∣ T + (T % R * N' % R) * N := by
  apply redc_dvd hN'
  rw [Nat.mod_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-- The REDC bound: `T < N·R` and `m < R` give `(T + m·N) / R < 2N`. -/
theorem redc_lt {N R : ℕ} (T m : ℕ) (hT : T < N * R) (hm : m < R) :
    (T + m * N) / R < 2 * N := by
  have hR : 0 < R := by omega
  rw [Nat.div_lt_iff_lt_mul hR]
  have : m * N ≤ R * N := Nat.mul_le_mul_right _ hm.le
  nlinarith

/-- The final conditional subtraction gives the canonical representative. -/
theorem condSub_eq_mod {N x : ℕ} (hx : x < 2 * N) :
    (if N ≤ x then x - N else x) = x % N := by
  split_ifs with h
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem condSub_lt {N x : ℕ} (hx : x < 2 * N) : (if N ≤ x then x - N else x) < N := by
  split_ifs with h <;> omega

theorem condSub_cast {N x : ℕ} (hx : x < 2 * N) :
    (((if N ≤ x then x - N else x) : ℕ) : ZMod N) = x := by
  rw [condSub_eq_mod hx, ZMod.natCast_mod]

/-- `ZMod.val` of a cast of a reduced number. -/
theorem val_cast_of_lt {N x : ℕ} (hx : x < N) : ((x : ZMod N)).val = x :=
  ZMod.val_natCast_of_lt hx

/-- Equality in `ZMod N` of two reduced numbers is equality of numbers. -/
theorem cast_inj_of_lt {N x y : ℕ} (hx : x < N) (hy : y < N) :
    (x : ZMod N) = (y : ZMod N) ↔ x = y := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-- Composition of reduction steps (word-by-word Montgomery): if `A₁ · R₁ ≡ A₀` and
`A₂ · R₂ ≡ A₁`, then `A₂ · (R₁ · R₂) ≡ A₀`. -/
theorem redc_step_cast {N : ℕ} {A₀ A₁ A₂ R₁ R₂ : ZMod N} (h₁ : A₁ * R₁ = A₀)
    (h₂ : A₂ * R₂ = A₁) : A₂ * (R₁ * R₂) = A₀ := by
  rw [← h₁, ← h₂]; ring

/-- Iterating a reduction step `k` times: if each step divides by `W` (`A (i+1) · W ≡ A i`),
then `A k · W^k ≡ A 0`. -/
theorem redc_iter_cast {N : ℕ} (W : ZMod N) (A : ℕ → ZMod N)
    (h : ∀ i, A (i + 1) * W = A i) (k : ℕ) : A k * W ^ k = A 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mul_assoc, mul_comm (A (k + 1) * W ^ k) W, ← ih, ← h k]; ring

/-- One CIOS-style step: `(A + c + m·N) / W ≡ (A + c) · W⁻¹`, stated multiplied out. -/
theorem redc_step_mul_cast {N W : ℕ} (A c m : ℕ) (h : W ∣ A + c + m * N) :
    (((A + c + m * N) / W : ℕ) : ZMod N) * (W : ZMod N) = A + c := by
  rw [redc_mul_cast (A + c) m h]; push_cast; ring

/-- Montgomery multiplication: if `a' ≡ a·R`, `b' ≡ b·R` and `X·R ≡ a'·b'`, then `X ≡ (a·b)·R`. -/
theorem mont_mul_cast {N : ℕ} {R a b a' b' X : ZMod N} (hR : IsUnit R) (ha : a' = a * R)
    (hb : b' = b * R) (hX : X * R = a' * b') : X = a * b * R := by
  apply hR.mul_right_cancel
  rw [hX, ha, hb]; ring

/-- Montgomery form: `x ↦ x·R`, inverted by multiplication with `R⁻¹` when `R` is a unit. -/
theorem mont_form_inj {N : ℕ} {R x y : ZMod N} (hR : IsUnit R) : x * R = y * R ↔ x = y :=
  ⟨hR.mul_right_cancel, fun h => by rw [h]⟩

theorem isUnit_cast_of_coprime {N R : ℕ} (h : Nat.Coprime R N) : IsUnit (R : ZMod N) :=
  (ZMod.unitOfCoprime R h).isUnit

end CC.Spec.Montgomery

namespace CC.Spec.P384

/-! ## Instances for P-384 -/

theorem coprime_two_pow_p (k : ℕ) : Nat.Coprime (2 ^ k) p :=
  Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two p_prime).2 (by decide +kernel))

theorem coprime_two_pow_n (k : ℕ) : Nat.Coprime (2 ^ k) n :=
  Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two n_prime).2 (by decide +kernel))

theorem p_lt_two_pow_384 : p < 2 ^ 384 := by decide +kernel

theorem n_lt_two_pow_384 : n < 2 ^ 384 := by decide +kernel

end CC.Spec.P384
