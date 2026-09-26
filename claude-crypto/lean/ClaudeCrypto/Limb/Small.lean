import ClaudeCrypto.Limb.Mac

/-! # Small generic IR blocks -/

namespace CC.Limb

/-- `(e, t) := t + c + 2^64 e` with `z = 0`, for a small `e`. -/
def addTop (t c e z : Var) : List Instr := [ .add t c, .adc e z ]

theorem addTop_exec (t c e z : Var) (s : State) (h1 : t ≠ c) (h2 : t ≠ e) (h3 : t ≠ z) (h4 : e ≠ c)
    (h5 : e ≠ z) (hz : s.r z = 0) (he : (s.r e).toNat + 1 < 2 ^ 64) :
    ∃ q, execBlock isa (addTop t c e z) s = some q ∧
      (q.1.r t).toNat + 2 ^ 64 * (q.1.r e).toNat = (s.r t).toNat + (s.r c).toNat + 2 ^ 64 * (s.r e).toNat ∧
      (∀ v, v ≠ t → v ≠ e → q.1.r v = s.r v) ∧
      q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  simp only [addTop]
  limb_sym
  simp only [Function.update_self, Function.update_of_ne, ne_eq, h1, h2, h3, h4, h5, h1.symm, h2.symm, h3.symm,
    h4.symm, h5.symm, not_false_eq_true, hz]
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · have := (s.r t).isLt; have := (s.r c).isLt
    simp only [Function.update_self, Function.update_of_ne, ne_eq, h2, h2.symm, not_false_eq_true]
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool, carryOut, Bool.toNat_false,
      Nat.add_zero, ble_toNat, toNat_zero64, Nat.reducePow, Nat.reduceMod]
    generalize (s.r t).toNat = T at *
    generalize (s.r c).toNat = C at *
    generalize (s.r e).toNat = E at *
    split_ifs <;> omega
  · intro v hv1 hv2
    simp only [Function.update_of_ne, ne_eq, hv1, hv2, not_false_eq_true]

/-- `r0 := lo := (t * mem[pk + off]) mod 2^64`, clobbering `x` and `hi`. -/
def qCompute (t pk : Var) (off : Nat) (x hi lo : Var) : List Instr :=
  [ .mov 0 t, .ld x pk off, .mulx hi lo x, .mov 0 lo ]

theorem qCompute_exec (t pk : Var) (off : Nat) (x hi lo : Var) (s : State)
    (h1 : x ≠ 0) (h2 : hi ≠ 0) (h3 : lo ≠ 0) (h4 : hi ≠ lo) (h5 : lo ≠ x) (h6 : x ≠ hi) (h7 : pk ≠ 0)
    (hp : InRegions (s.rd ++ s.wr) (s.r pk + BitVec.ofNat 64 off) 8) :
    ∃ q, execBlock isa (qCompute t pk off x hi lo) s = some q ∧
      (q.1.r 0).toNat = (s.r t).toNat * (s.mem.readW (s.r pk + BitVec.ofNat 64 off) 64).toNat % 2 ^ 64 ∧
      (∀ v, v ≠ 0 → v ≠ x → v ≠ hi → v ≠ lo → q.1.r v = s.r v) ∧
      q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  have hm : ¬ (hi = lo ∨ lo = 0 ∨ lo = x) := by
    rintro (h | h | h)
    · exact h4 h
    · exact h3 h
    · exact h5 h
  simp only [qCompute]
  limb_sym [h1, h2, h3, h4, h5, h6, h7, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, hp, hm]
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [State.set_r, Function.update_self, BitVec.toNat_ofNat]
  · intro v hv1 hv2 hv3 hv4
    simp only [State.set_r, Function.update_of_ne, ne_eq, hv1, hv2, hv3, hv4, not_false_eq_true]

end CC.Limb
