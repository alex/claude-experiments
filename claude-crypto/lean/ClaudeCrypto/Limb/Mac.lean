import ClaudeCrypto.Limb.Sym

/-! # Multiply-accumulate: the inner step of multi-precision multiplication -/

namespace CC.Limb

/-- `(hi, t) := t + r0 * x + c` (as a two-word result); `lo` is scratch and `z` holds zero. -/
def mac (t x c hi lo z : Var) : List Instr :=
  [ .mulx hi lo x, .add lo c, .adc hi z, .add t lo, .adc hi z ]

theorem toNat_add_lt (a b : BitVec 64) (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem ble_toNat (a b : Nat) : (Nat.ble a b).toNat = if a ≤ b then 1 else 0 := by
  by_cases h : a ≤ b
  · have : Nat.ble a b = true := by rwa [Nat.ble_eq]
    simp [this, h]
  · have : Nat.ble a b = false := by rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; exact h
    simp [this, h]

theorem blt_toNat (a b : Nat) : (Nat.blt a b).toNat = if a < b then 1 else 0 := by
  by_cases h : a < b
  · have : Nat.blt a b = true := by rwa [Nat.blt_eq]
    simp [this, h]
  · have : Nat.blt a b = false := by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact h
    simp [this, h]

theorem toNat_zero64 : (0 : BitVec 64).toNat = 0 := rfl

theorem mac_exec (t x c hi lo z : Var) (s : State)
    (h1 : t ≠ x) (h2 : t ≠ c) (h3 : t ≠ hi) (h4 : t ≠ lo) (h5 : t ≠ z) (h6 : x ≠ lo) (h7 : x ≠ hi)
    (h8 : c ≠ hi) (h9 : c ≠ lo) (h10 : hi ≠ lo) (h11 : hi ≠ z) (h12 : lo ≠ z) (h13 : lo ≠ 0) (h14 : hi ≠ 0)
    (h15 : t ≠ 0) (hz : s.r z = 0) :
    ∃ q, execBlock isa (mac t x c hi lo z) s = some q ∧
      (q.1.r t).toNat + 2 ^ 64 * (q.1.r hi).toNat =
        (s.r t).toNat + (s.r 0).toNat * (s.r x).toNat + (s.r c).toNat ∧
      (∀ v, v ≠ t → v ≠ hi → v ≠ lo → q.1.r v = s.r v) ∧ q.1.cf = some false ∧ q.1.sub = false ∧
      q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  simp only [mac]
  have hm : ¬ (hi = lo ∨ lo = 0 ∨ lo = x) := by
    rintro (h | h | h)
    · exact h10 h
    · exact h13 h
    · exact h6 h.symm
  limb_sym
  simp only [hm, ite_false, Option.map_some, Option.bind_some, Function.update_self, Function.update_of_ne,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h1.symm, h2.symm, h3.symm, h4.symm,
    h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm, h11.symm, h12.symm, h13.symm, h14.symm, h15.symm,
    ne_eq, not_false_eq_true, CC.Limb.State.set_r, hz, or_self, reduceIte]
  refine ⟨_, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [Function.update_self, Function.update_of_ne, ne_eq, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm,
      h11.symm, h12.symm, h13.symm, h14.symm, h15.symm, not_false_eq_true]
    have hPb : (s.r 0).toNat * (s.r x).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by have := (s.r 0).isLt; omega) (by have := (s.r x).isLt; omega)
    generalize (s.r 0).toNat * (s.r x).toNat = P at hPb ⊢
    have := (s.r t).isLt; have := (s.r c).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool, carryOut,
      BitVec.toNat_zero, Nat.add_zero, Bool.toNat_false]
    generalize (s.r t).toNat = T at *
    generalize (s.r c).toNat = C at *
    simp only [ble_toNat, toNat_zero64, Nat.add_zero, Nat.reducePow, Nat.reduceMod]
    split_ifs <;> omega
  · intro v hv1 hv2 hv3
    simp only [Function.update_of_ne, ne_eq, hv1, hv2, hv3, not_false_eq_true]
  · have hPb : (s.r 0).toNat * (s.r x).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by have := (s.r 0).isLt; omega) (by have := (s.r x).isLt; omega)
    generalize (s.r 0).toNat * (s.r x).toNat = P at hPb ⊢
    have := (s.r t).isLt; have := (s.r c).isLt
    simp only [carryOut, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
      Bool.toNat_false, Nat.add_zero, ble_toNat, toNat_zero64, Nat.reducePow, Nat.reduceMod, Option.some.injEq]
    generalize (s.r t).toNat = T at *
    generalize (s.r c).toNat = C at *
    rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]
    split_ifs <;> omega

/-- `mac` with the second factor in the carry-out register: `(hi, t) := t + r0 * hi + c`. -/
def mac2 (t c hi lo z : Var) : List Instr :=
  [ .mulx hi lo hi, .add lo c, .adc hi z, .add t lo, .adc hi z ]

theorem mac2_exec (t c hi lo z : Var) (s : State)
    (h2 : t ≠ c) (h3 : t ≠ hi) (h4 : t ≠ lo) (h5 : t ≠ z)
    (h8 : c ≠ hi) (h9 : c ≠ lo) (h10 : hi ≠ lo) (h11 : hi ≠ z) (h12 : lo ≠ z) (h13 : lo ≠ 0) (h14 : hi ≠ 0)
    (h15 : t ≠ 0) (hz : s.r z = 0) :
    ∃ q, execBlock isa (mac2 t c hi lo z) s = some q ∧
      (q.1.r t).toNat + 2 ^ 64 * (q.1.r hi).toNat =
        (s.r t).toNat + (s.r 0).toNat * (s.r hi).toNat + (s.r c).toNat ∧
      (∀ v, v ≠ t → v ≠ hi → v ≠ lo → q.1.r v = s.r v) ∧ q.1.cf = some false ∧ q.1.sub = false ∧
      q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  simp only [mac2]
  have hm : ¬ (hi = lo ∨ lo = 0 ∨ lo = hi) := by
    rintro (h | h | h)
    · exact h10 h
    · exact h13 h
    · exact h10 h.symm
  limb_sym
  simp only [hm, ite_false, Option.map_some, Option.bind_some, Function.update_self, Function.update_of_ne,
    h2, h3, h4, h5, h8, h9, h10, h11, h12, h13, h14, h15, h2.symm, h3.symm, h4.symm,
    h5.symm, h8.symm, h9.symm, h10.symm, h11.symm, h12.symm, h13.symm, h14.symm, h15.symm,
    ne_eq, not_false_eq_true, CC.Limb.State.set_r, hz, or_self, reduceIte]
  have hPb : (s.r 0).toNat * (s.r hi).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := (s.r 0).isLt; omega) (by have := (s.r hi).isLt; omega)
  have := (s.r t).isLt; have := (s.r c).isLt
  refine ⟨_, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [Function.update_self, Function.update_of_ne, ne_eq, h2, h3, h4, h5, h8, h9, h10, h11,
      h12, h13, h14, h15, h2.symm, h3.symm, h4.symm, h5.symm, h8.symm, h9.symm, h10.symm,
      h11.symm, h12.symm, h13.symm, h14.symm, h15.symm, not_false_eq_true]
    generalize (s.r 0).toNat * (s.r hi).toNat = P at hPb ⊢
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool, carryOut,
      BitVec.toNat_zero, Nat.add_zero, Bool.toNat_false]
    generalize (s.r t).toNat = T at *
    generalize (s.r c).toNat = C at *
    simp only [ble_toNat, toNat_zero64, Nat.add_zero, Nat.reducePow, Nat.reduceMod]
    split_ifs <;> omega
  · intro v hv1 hv2 hv3
    simp only [Function.update_of_ne, ne_eq, hv1, hv2, hv3, not_false_eq_true]
  · generalize (s.r 0).toNat * (s.r hi).toNat = P at hPb ⊢
    simp only [carryOut, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
      Bool.toNat_false, Nat.add_zero, ble_toNat, toNat_zero64, Nat.reducePow, Nat.reduceMod, Option.some.injEq]
    generalize (s.r t).toNat = T at *
    generalize (s.r c).toNat = C at *
    rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]
    split_ifs <;> omega

end CC.Limb
