import ClaudeCrypto.Spec.P384

/-!
# P-384: Jacobian-coordinate formulas

Algebraic correctness of the Jacobian-coordinate point formulas (for `a = −3`)
used by the P-384 implementations, stated in terms of the specification's
`Point`, `mkPoint` and `F`:

* `Jrep X Y Z P`: the Jacobian triple `(X, Y, Z)` represents the point `P`
  (`Z = 0` for the point at infinity, otherwise `P = (X/Z², Y/Z³)`);
* `jrep_dbl`: doubling, `dbl-2001-b`;
* `jrep_madd`: mixed addition with an affine point, `madd-2007-bl`;
* `jrep_add`: addition of two Jacobian points, `add-2007-bl`;
* `jrep_x_mod_n_eq_iff`: the final ECDSA comparison `x_R mod n = r` without
  inverting `Z`.
-/

-- `p` is `2 ^ 384 - …`; let the elaborator evaluate it when checking definitional equalities.
set_option exponentiation.threshold 1000

namespace CC.Spec.P384

open WeierstrassCurve WeierstrassCurve.Affine

/-- `(X, Y, Z)` (Jacobian coordinates) represents the point `P`. -/
def Jrep (X Y Z : F) (P : Point) : Prop :=
  if Z = 0 then P = 0 else ∃ h, P = mkPoint (X / Z ^ 2) (Y / Z ^ 3) h

/-! ## Basic facts about `F` and the curve -/

theorem two_ne_zero_F : (2 : F) ≠ 0 := by decide +kernel

theorem n_lt_p : n < p := by decide +kernel

theorem p_lt_two_n : p < 2 * n := by decide +kernel

theorem curve_a₁ : curve.a₁ = 0 := rfl
theorem curve_a₂ : curve.a₂ = 0 := rfl
theorem curve_a₃ : curve.a₃ = 0 := rfl
theorem curve_a₄ : curve.a₄ = -3 := rfl

theorem curve_negY (x y : F) : curve.toAffine.negY x y = -y := by
  simp [Affine.negY, curve_a₁, curve_a₃]

theorem curve_addX (x₁ x₂ ℓ : F) : curve.toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - x₁ - x₂ := by
  simp [Affine.addX, curve_a₁, curve_a₂]

theorem curve_addY (x₁ x₂ y₁ ℓ : F) :
    curve.toAffine.addY x₁ x₂ y₁ ℓ = ℓ * (x₁ - (ℓ ^ 2 - x₁ - x₂)) - y₁ := by
  simp only [Affine.addY, Affine.negAddY, curve_negY, curve_addX]; ring

theorem mkPoint_eq_some (x y : F) (h : OnCurve x y) :
    ∃ hns, mkPoint x y h = Affine.Point.some x y hns := ⟨_, rfl⟩

theorem mkPoint_nonsingular {x y : F} (h : OnCurve x y) : curve.toAffine.Nonsingular x y :=
  Affine.equation_iff_nonsingular.mp ((curve_equation_iff x y).mpr h)

theorem mkPoint_def {x y : F} (h : OnCurve x y) :
    mkPoint x y h = Affine.Point.some x y (mkPoint_nonsingular h) := rfl

theorem onCurve_of_nonsingular {x y : F} (h : curve.toAffine.Nonsingular x y) : OnCurve x y :=
  (curve_equation_iff x y).mp h.1

theorem some_eq_mkPoint {x y x' y' : F} (hns : curve.toAffine.Nonsingular x y)
    (hx : x = x') (hy : y = y') : ∃ h, Affine.Point.some x y hns = mkPoint x' y' h := by
  subst hx hy; exact ⟨onCurve_of_nonsingular hns, rfl⟩

theorem mkPoint_ne_zero {x y : F} (h : OnCurve x y) : mkPoint x y h ≠ 0 :=
  Affine.Point.some_ne_zero _

theorem mkPoint_inj {x y x' y' : F} {h : OnCurve x y} {h' : OnCurve x' y'} :
    mkPoint x y h = mkPoint x' y' h' ↔ x = x' ∧ y = y' := by
  constructor
  · intro e; rw [mkPoint_def, mkPoint_def] at e; exact Affine.Point.some.inj e
  · rintro ⟨rfl, rfl⟩; rfl

/-- Two affine points with the same `x`: they are equal or opposite. -/
theorem onCurve_y_eq_or {x y₁ y₂ : F} (h₁ : OnCurve x y₁) (h₂ : OnCurve x y₂) :
    y₁ = y₂ ∨ y₁ = -y₂ := by
  have := Affine.Y_eq_of_X_eq ((curve_equation_iff x y₁).mpr h₁)
    ((curve_equation_iff x y₂).mpr h₂) rfl
  rwa [curve_negY] at this

/-! ## Affine group law, in the form used below -/

/-- Addition of two affine points with different `x`. -/
theorem mkPoint_add_of_x_ne {x₁ y₁ x₂ y₂ x₃ y₃ : F} (h₁ : OnCurve x₁ y₁) (h₂ : OnCurve x₂ y₂)
    (hx : x₁ ≠ x₂)
    (hx₃ : x₃ = ((y₁ - y₂) / (x₁ - x₂)) ^ 2 - x₁ - x₂)
    (hy₃ : y₃ = (y₁ - y₂) / (x₁ - x₂) * (x₁ - x₃) - y₁) :
    ∃ h₃, mkPoint x₁ y₁ h₁ + mkPoint x₂ y₂ h₂ = mkPoint x₃ y₃ h₃ := by
  rw [mkPoint_def h₁, mkPoint_def h₂, Affine.Point.add_of_X_ne hx]
  apply some_eq_mkPoint
  · rw [curve_addX, Affine.slope_of_X_ne hx, hx₃]
  · rw [curve_addY, Affine.slope_of_X_ne hx, hy₃, hx₃]

/-- Doubling of an affine point with `y ≠ 0`. -/
theorem mkPoint_add_self_of_y_ne {x y x₃ y₃ : F} (h : OnCurve x y) (hy : y ≠ 0)
    (hx₃ : x₃ = ((3 * x ^ 2 - 3) / (2 * y)) ^ 2 - 2 * x)
    (hy₃ : y₃ = (3 * x ^ 2 - 3) / (2 * y) * (x - x₃) - y) :
    ∃ h₃, mkPoint x y h + mkPoint x y h = mkPoint x₃ y₃ h₃ := by
  have hy' : y ≠ curve.toAffine.negY x y := by
    rw [curve_negY]; intro e
    have h2 : 2 * y = 0 := by linear_combination (e : y = -y)
    exact hy ((mul_eq_zero.1 h2).resolve_left two_ne_zero_F)
  have hsl : curve.toAffine.slope x x y y = (3 * x ^ 2 - 3) / (2 * y) := by
    rw [Affine.slope_of_Y_ne rfl hy', curve_negY, curve_a₁, curve_a₂, curve_a₄]
    have e1 : 3 * x ^ 2 + 2 * 0 * x + -3 - 0 * y = 3 * x ^ 2 - 3 := by ring
    have e2 : y - -y = 2 * y := by ring
    rw [e1, e2]
  rw [mkPoint_def h, Affine.Point.add_self_of_Y_ne hy']
  apply some_eq_mkPoint
  · rw [curve_addX, hsl, hx₃]; ring
  · rw [curve_addY, hsl, hy₃, hx₃]; ring

/-- Doubling of an affine point with `y = 0` gives `0`. -/
theorem mkPoint_add_self_of_y_eq {x y : F} (h : OnCurve x y) (hy : y = 0) :
    mkPoint x y h + mkPoint x y h = 0 := by
  rw [mkPoint_def h]
  apply Affine.Point.add_self_of_Y_eq
  rw [curve_negY, hy, neg_zero]

/-- Two affine points with the same `x` and opposite `y ≠ 0` sum to `0`. -/
theorem mkPoint_add_of_y_ne {x₁ y₁ x₂ y₂ : F} (h₁ : OnCurve x₁ y₁) (h₂ : OnCurve x₂ y₂)
    (hx : x₁ = x₂) (hy : y₁ ≠ y₂) : mkPoint x₁ y₁ h₁ + mkPoint x₂ y₂ h₂ = 0 := by
  subst hx
  rw [mkPoint_def h₁, mkPoint_def h₂]
  apply Affine.Point.add_of_Y_eq rfl
  rw [curve_negY]
  exact (onCurve_y_eq_or h₁ h₂).resolve_left hy

/-! ## `Jrep` basics -/

theorem jrep_zero_iff {X Y Z : F} {P : Point} (hZ : Z = 0) : Jrep X Y Z P ↔ P = 0 := by
  simp [Jrep, hZ]

theorem jrep_of_ne {X Y Z : F} {P : Point} (hZ : Z ≠ 0) :
    Jrep X Y Z P ↔ ∃ h, P = mkPoint (X / Z ^ 2) (Y / Z ^ 3) h := by
  simp [Jrep, hZ]

/-- A Jacobian triple with `Z ≠ 0` represents a (unique) affine point. -/
theorem jrep_mk {X Y Z x y : F} (hZ : Z ≠ 0) (h : OnCurve x y) (hx : x = X / Z ^ 2)
    (hy : y = Y / Z ^ 3) : Jrep X Y Z (mkPoint x y h) := by
  subst hx hy; exact (jrep_of_ne hZ).2 ⟨h, rfl⟩

/-- An affine point `(x, y)` is represented by `(x, y, 1)`. -/
theorem jrep_affine {x y : F} (h : OnCurve x y) : Jrep x y 1 (mkPoint x y h) :=
  jrep_mk one_ne_zero h (by simp) (by simp)

/-- `0` is represented by any triple with `Z = 0`. -/
theorem jrep_zero (X Y : F) : Jrep X Y 0 0 := (jrep_zero_iff rfl).2 rfl

theorem jrep_of_exists {X Y Z x y : F} {P : Point} (hZ : Z ≠ 0)
    (h : ∃ h, P = mkPoint x y h) (hx : x = X / Z ^ 2) (hy : y = Y / Z ^ 3) : Jrep X Y Z P := by
  obtain ⟨h, rfl⟩ := h; exact jrep_mk hZ h hx hy

/-! ## Doubling: `dbl-2001-b` (`a = −3`) -/

/-- `dbl-2001-b` computes `2 • P`, in all cases (including `P = 0` and `y = 0`). -/
theorem jrep_dbl {X Y Z : F} {P : Point} (hP : Jrep X Y Z P) :
    let δ := Z ^ 2
    let γ := Y ^ 2
    let β := X * γ
    let α := 3 * (X - δ) * (X + δ)
    let X₃ := α ^ 2 - 8 * β
    let Z₃ := (Y + Z) ^ 2 - γ - δ
    let Y₃ := α * (4 * β - X₃) - 8 * γ ^ 2
    Jrep X₃ Y₃ Z₃ (2 • P) := by
  intro δ γ β α X₃ Z₃ Y₃
  have hZ₃ : Z₃ = 2 * Y * Z := by simp only [Z₃, γ, δ]; ring
  rw [two_nsmul]
  by_cases hZ : Z = 0
  · rw [jrep_zero_iff hZ] at hP
    rw [jrep_zero_iff (by rw [hZ₃, hZ, mul_zero]), hP, add_zero]
  rw [jrep_of_ne hZ] at hP
  obtain ⟨h, rfl⟩ := hP
  by_cases hY : Y = 0
  · rw [jrep_zero_iff (by rw [hZ₃, hY, mul_zero, zero_mul])]
    exact mkPoint_add_self_of_y_eq h (by rw [hY, zero_div])
  have hZ₃0 : Z₃ ≠ 0 := by rw [hZ₃]; exact mul_ne_zero (mul_ne_zero two_ne_zero_F hY) hZ
  have hy : Y / Z ^ 3 ≠ 0 := div_ne_zero hY (pow_ne_zero _ hZ)
  have h2 := two_ne_zero_F
  refine jrep_of_exists hZ₃0 (mkPoint_add_self_of_y_ne h hy rfl rfl) ?_ ?_
  · rw [hZ₃]; simp only [X₃, α, β, γ, δ]
    field_simp
    ring
  · rw [hZ₃]; simp only [Y₃, X₃, α, β, γ, δ]
    field_simp
    ring

/-! ## Mixed addition: `madd-2007-bl` -/

/-- `madd-2007-bl`: adding the affine point `Q = (x₂, y₂)` to the Jacobian point
`(X₁, Y₁, Z₁)`.  The formulas are correct when `Z₁ ≠ 0` and `H ≠ 0`; otherwise the caller
must handle `P = 0` (result `Q`), `P = Q` (`H = 0`, `r = 0`: double instead) and `P = −Q`
(`H = 0`, `r ≠ 0`: result `0`). -/
theorem jrep_madd {X₁ Y₁ Z₁ x₂ y₂ : F} {P : Point} (h₂ : OnCurve x₂ y₂)
    (hP : Jrep X₁ Y₁ Z₁ P) :
    let Z1Z1 := Z₁ ^ 2
    let U₂ := x₂ * Z1Z1
    let S₂ := y₂ * Z₁ * Z1Z1
    let H := U₂ - X₁
    let HH := H ^ 2
    let I := 4 * HH
    let J := H * I
    let r := 2 * (S₂ - Y₁)
    let V := X₁ * I
    let X₃ := r ^ 2 - J - 2 * V
    let Y₃ := r * (V - X₃) - 2 * Y₁ * J
    let Z₃ := (Z₁ + H) ^ 2 - Z1Z1 - HH
    (Z₁ = 0 → P + mkPoint x₂ y₂ h₂ = mkPoint x₂ y₂ h₂) ∧
    (Z₁ ≠ 0 → H ≠ 0 → Jrep X₃ Y₃ Z₃ (P + mkPoint x₂ y₂ h₂)) ∧
    (Z₁ ≠ 0 → H = 0 → r = 0 → P = mkPoint x₂ y₂ h₂) ∧
    (Z₁ ≠ 0 → H = 0 → r ≠ 0 → P + mkPoint x₂ y₂ h₂ = 0) := by
  intro Z1Z1 U₂ S₂ H HH I J r V X₃ Y₃ Z₃
  refine ⟨fun hZ => ?_, fun hZ hH => ?_, fun hZ hH hr => ?_, fun hZ hH hr => ?_⟩
  · rw [(jrep_zero_iff hZ).1 hP, zero_add]
  all_goals
    rw [jrep_of_ne hZ] at hP
    obtain ⟨h₁, rfl⟩ := hP
  · have h2 := two_ne_zero_F
    have hx : X₁ / Z₁ ^ 2 ≠ x₂ := by
      intro e; apply hH; simp only [H, U₂, Z1Z1]; rw [← e]; field_simp; ring
    have hH' : X₁ - x₂ * Z₁ ^ 2 ≠ 0 := by
      intro e; apply hH; simp only [H, U₂, Z1Z1]; linear_combination -e
    have hZ₃ : Z₃ = 2 * Z₁ * H := by simp only [Z₃, HH, Z1Z1]; ring
    have hZ₃0 : Z₃ ≠ 0 := by rw [hZ₃]; exact mul_ne_zero (mul_ne_zero h2 hZ) hH
    have hl : (Y₁ / Z₁ ^ 3 - y₂) / (X₁ / Z₁ ^ 2 - x₂) = r / Z₃ := by
      rw [div_eq_div_iff (sub_ne_zero.2 hx) hZ₃0, hZ₃]
      simp only [r, H, S₂, U₂, Z1Z1]
      field_simp
      ring
    have ex₂ : x₂ = (X₁ + H) / Z₁ ^ 2 := by simp only [H, U₂, Z1Z1]; field_simp; ring
    have eX₃ : X₃ = r ^ 2 - 4 * H ^ 3 - 8 * X₁ * H ^ 2 := by simp only [X₃, V, J, I, HH]; ring
    have eY₃ : Y₃ = r * (4 * X₁ * H ^ 2 - X₃) - 8 * Y₁ * H ^ 3 := by
      simp only [Y₃, V, J, I, HH]; ring
    refine jrep_of_exists hZ₃0 (mkPoint_add_of_x_ne h₁ h₂ hx rfl rfl) ?_ ?_
    · rw [hl, hZ₃, eX₃, ex₂]
      clear_value Z1Z1 U₂ S₂ H HH I J r V X₃ Y₃ Z₃
      field_simp
      ring
    · rw [hl, hZ₃, eY₃, eX₃, ex₂]
      clear_value Z1Z1 U₂ S₂ H HH I J r V X₃ Y₃ Z₃
      field_simp
      ring
  · rw [mkPoint_inj]
    constructor
    · field_simp; linear_combination -hH
    · have : y₂ * Z₁ ^ 3 - Y₁ = 0 := by
        have := (mul_eq_zero.1 hr).resolve_left two_ne_zero_F
        linear_combination this
      field_simp; linear_combination -this
  · apply mkPoint_add_of_y_ne h₁ h₂
    · field_simp; linear_combination -hH
    · intro e; apply hr; simp only [r, S₂, Z1Z1]; rw [← e]; field_simp; ring

/-! ## Addition of two Jacobian points: `add-2007-bl` -/

/-- `add-2007-bl`: adding two Jacobian points.  The formulas are correct when
`Z₁ ≠ 0`, `Z₂ ≠ 0` and `H ≠ 0`; otherwise the caller must handle `P = 0` (result `Q`),
`Q = 0` (result `P`), `P = Q` (`H = 0`, `r = 0`: double instead) and `P = −Q`
(`H = 0`, `r ≠ 0`: result `0`). -/
theorem jrep_add {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : F} {P Q : Point} (hP : Jrep X₁ Y₁ Z₁ P)
    (hQ : Jrep X₂ Y₂ Z₂ Q) :
    let Z1Z1 := Z₁ ^ 2
    let Z2Z2 := Z₂ ^ 2
    let U₁ := X₁ * Z2Z2
    let U₂ := X₂ * Z1Z1
    let S₁ := Y₁ * Z₂ * Z2Z2
    let S₂ := Y₂ * Z₁ * Z1Z1
    let H := U₂ - U₁
    let I := (2 * H) ^ 2
    let J := H * I
    let r := 2 * (S₂ - S₁)
    let V := U₁ * I
    let X₃ := r ^ 2 - J - 2 * V
    let Y₃ := r * (V - X₃) - 2 * S₁ * J
    let Z₃ := ((Z₁ + Z₂) ^ 2 - Z1Z1 - Z2Z2) * H
    (Z₁ = 0 → P + Q = Q) ∧
    (Z₂ = 0 → P + Q = P) ∧
    (Z₁ ≠ 0 → Z₂ ≠ 0 → H ≠ 0 → Jrep X₃ Y₃ Z₃ (P + Q)) ∧
    (Z₁ ≠ 0 → Z₂ ≠ 0 → H = 0 → r = 0 → P = Q) ∧
    (Z₁ ≠ 0 → Z₂ ≠ 0 → H = 0 → r ≠ 0 → P + Q = 0) := by
  intro Z1Z1 Z2Z2 U₁ U₂ S₁ S₂ H I J r V X₃ Y₃ Z₃
  refine ⟨fun hZ => ?_, fun hZ => ?_, fun hZ₁ hZ₂ hH => ?_, fun hZ₁ hZ₂ hH hr => ?_,
    fun hZ₁ hZ₂ hH hr => ?_⟩
  · rw [(jrep_zero_iff hZ).1 hP, zero_add]
  · rw [(jrep_zero_iff hZ).1 hQ, add_zero]
  all_goals
    rw [jrep_of_ne hZ₁] at hP
    rw [jrep_of_ne hZ₂] at hQ
    obtain ⟨h₁, rfl⟩ := hP
    obtain ⟨h₂, rfl⟩ := hQ
  · have h2 := two_ne_zero_F
    have hx : X₁ / Z₁ ^ 2 ≠ X₂ / Z₂ ^ 2 := by
      intro e; apply hH; simp only [H, U₁, U₂, Z1Z1, Z2Z2]
      rw [div_eq_div_iff (pow_ne_zero _ hZ₁) (pow_ne_zero _ hZ₂)] at e
      linear_combination -e
    have hZ₃ : Z₃ = 2 * Z₁ * Z₂ * H := by simp only [Z₃, Z1Z1, Z2Z2]; ring
    have hZ₃0 : Z₃ ≠ 0 := by
      rw [hZ₃]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hZ₁) hZ₂) hH
    have hl : (Y₁ / Z₁ ^ 3 - Y₂ / Z₂ ^ 3) / (X₁ / Z₁ ^ 2 - X₂ / Z₂ ^ 2) = r / Z₃ := by
      rw [div_eq_div_iff (sub_ne_zero.2 hx) hZ₃0, hZ₃]
      simp only [r, H, S₁, S₂, U₁, U₂, Z1Z1, Z2Z2]
      field_simp
      ring
    have eX₁ : X₁ = U₁ / Z₂ ^ 2 := by simp only [U₁, Z2Z2]; field_simp
    have eX₂ : X₂ = (U₁ + H) / Z₁ ^ 2 := by simp only [H, U₁, U₂, Z1Z1, Z2Z2]; field_simp; ring
    have eY₁ : Y₁ = S₁ / Z₂ ^ 3 := by simp only [S₁, Z2Z2]; field_simp
    have eX₃ : X₃ = r ^ 2 - 4 * H ^ 3 - 8 * U₁ * H ^ 2 := by simp only [X₃, V, J, I]; ring
    have eY₃ : Y₃ = r * (4 * U₁ * H ^ 2 - X₃) - 8 * S₁ * H ^ 3 := by
      simp only [Y₃, V, J, I]; ring
    refine jrep_of_exists hZ₃0 (mkPoint_add_of_x_ne h₁ h₂ hx rfl rfl) ?_ ?_
    · rw [hl, hZ₃, eX₃]
      clear_value Z1Z1 Z2Z2 U₁ U₂ S₁ S₂ H I J r V X₃ Y₃ Z₃
      subst eX₁ eX₂
      field_simp
      ring
    · rw [hl, hZ₃, eY₃, eX₃]
      clear_value Z1Z1 Z2Z2 U₁ U₂ S₁ S₂ H I J r V X₃ Y₃ Z₃
      subst eX₁ eX₂ eY₁
      field_simp
      ring
  · rw [mkPoint_inj]
    constructor
    · rw [div_eq_div_iff (pow_ne_zero _ hZ₁) (pow_ne_zero _ hZ₂)]
      linear_combination -hH
    · have : Y₂ * Z₁ ^ 3 - Y₁ * Z₂ ^ 3 = 0 := by
        have := (mul_eq_zero.1 hr).resolve_left two_ne_zero_F
        linear_combination this
      rw [div_eq_div_iff (pow_ne_zero _ hZ₁) (pow_ne_zero _ hZ₂)]
      linear_combination -this
  · apply mkPoint_add_of_y_ne h₁ h₂
    · rw [div_eq_div_iff (pow_ne_zero _ hZ₁) (pow_ne_zero _ hZ₂)]
      linear_combination -hH
    · intro e; apply hr
      rw [div_eq_div_iff (pow_ne_zero _ hZ₁) (pow_ne_zero _ hZ₂)] at e
      simp only [r, S₁, S₂, Z1Z1, Z2Z2]
      linear_combination -2 * e

/-! ## The final ECDSA comparison, without inverting `Z` -/

theorem eq_natCast_iff_val_eq {x : F} {c : ℕ} (hc : c < p) : x = (c : F) ↔ x.val = c := by
  constructor
  · rintro rfl; exact ZMod.val_natCast_of_lt hc
  · intro h; rw [← h, ZMod.natCast_zmod_val]

/-- For `R = (x_R, y_R)` represented by `(X, Y, Z)`, the check `x_R mod n = r` of FIPS 186-5
§6.4.2 step 7–8 can be done as `X = r·Z²` or (when `r + n < p`) `X = (r + n)·Z²`. -/
theorem jrep_x_mod_n_eq_iff {X Y Z : F} {R : Point} (hR : Jrep X Y Z R) (hZ : Z ≠ 0)
    {xR yR : F} {h : curve.toAffine.Nonsingular xR yR} (hRe : R = .some xR yR h)
    {r : ℕ} (hr : r < n) :
    xR.val % n = r ↔ (X = (r : F) * Z ^ 2 ∨ (r + n < p ∧ X = ((r + n : ℕ) : F) * Z ^ 2)) := by
  obtain ⟨h', hR'⟩ := (jrep_of_ne hZ).1 hR
  rw [hRe, mkPoint_def] at hR'
  have hx : xR = X / Z ^ 2 := (Affine.Point.some.inj hR').1
  have hZ2 : Z ^ 2 ≠ 0 := pow_ne_zero _ hZ
  have hX : ∀ c : F, X = c * Z ^ 2 ↔ xR = c := by
    intro c; rw [hx, div_eq_iff hZ2]
  rw [hX, hX]
  have hnp := n_lt_p
  have hpn := p_lt_two_n
  have hv : xR.val < p := ZMod.val_lt xR
  have e1 : xR = (r : F) ↔ xR.val = r := eq_natCast_iff_val_eq (by omega)
  have e2 : r + n < p → (xR = ((r + n : ℕ) : F) ↔ xR.val = r + n) :=
    fun h => eq_natCast_iff_val_eq h
  rw [e1]
  set v := xR.val
  constructor
  · intro hm
    rcases lt_or_ge v n with hvn | hvn
    · rw [Nat.mod_eq_of_lt hvn] at hm; exact Or.inl hm
    · have : v % n = v - n := by rw [Nat.mod_eq_sub_mod hvn, Nat.mod_eq_of_lt (by omega)]
      right
      have h1 : r + n < p := by omega
      exact ⟨h1, (e2 h1).2 (by omega)⟩
  · rintro (hm | ⟨h1, hm⟩)
    · rw [hm, Nat.mod_eq_of_lt hr]
    · rw [(e2 h1).1 hm, Nat.add_mod_right, Nat.mod_eq_of_lt hr]

end CC.Spec.P384
