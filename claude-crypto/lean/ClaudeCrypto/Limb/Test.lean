import ClaudeCrypto.Limb.FProg

/-! # Testing a slot for zero -/

namespace CC.Limb

/-- `r d := OR of the six limbs at r14 + off` (`r9` scratch). -/
def orSlot (d : Var) (off : Nat) : List Instr :=
  [ .ld d 14 off, .ld 9 14 (off + 8), .or d 9, .ld 9 14 (off + 16), .or d 9, .ld 9 14 (off + 24), .or d 9,
    .ld 9 14 (off + 32), .or d 9, .ld 9 14 (off + 40), .or d 9 ]

theorem or_eq_zero (a b : BitVec 64) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      have := congrArg (fun x => x.getLsbD i) h <;> simp at this <;> simp [this]
  · rintro ⟨rfl, rfl⟩; simp

theorem lsum6_eq_zero (f : Nat → Nat) : lsum f 6 = 0 ↔ ∀ k < 6, f k = 0 := by
  simp only [lsum]
  constructor
  · intro h k hk
    interval_cases k <;> simp_all [pow_pos] <;> omega
  · intro h
    simp [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega)]

theorem orSlot_exec (d : Var) (off : Nat) (s : State) (hd9 : d ≠ 9) (hd14 : d ≠ 14)
    (hp : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.r 14 + BitVec.ofNat 64 (off + 8 * k)) 8) :
    ∃ q, execBlock isa (orSlot d off) s = some q ∧
      (q.1.r d = 0 ↔ mval s.mem (s.r 14 + BitVec.ofNat 64 off) 6 = 0) ∧
      (∀ v, v ≠ d → v ≠ 9 → q.1.r v = s.r v) ∧ q.1.cf = none ∧
      q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  have p0 := hp 0 (by decide); have p1 := hp 1 (by decide); have p2 := hp 2 (by decide)
  have p3 := hp 3 (by decide); have p4 := hp 4 (by decide); have p5 := hp 5 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at p0 p1 p2 p3 p4 p5
  have h9 : (9 : Var) ≠ 14 := by decide
  simp only [orSlot]
  limb_sym [p0, p1, p2, p3, p4, p5, hd9, hd14, hd9.symm, hd14.symm, h9]
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [Function.update_self, or_eq_zero]
    unfold mval
    rw [lsum6_eq_zero]
    constructor
    · rintro ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ k hk
      unfold mlimb
      interval_cases k <;> simp_all [addr_add_ofNat']
    · intro h
      have e : ∀ k < 6, s.mem.readW (s.r 14 + BitVec.ofNat 64 (off + 8 * k)) 64 = 0 := fun k hk => by
        have := h k hk; unfold mlimb at this; rw [addr_add_ofNat'] at this
        exact BitVec.eq_of_toNat_eq (by simpa using this)
      have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
      have e3 := e 3 (by decide); have e4 := e 4 (by decide); have e5 := e 5 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at e0 e1 e2 e3 e4 e5
      exact ⟨⟨⟨⟨⟨e0, e1⟩, e2⟩, e3⟩, e4⟩, e5⟩
  · intro v hv1 hv2
    simp only [Function.update_of_ne hv1, Function.update_of_ne hv2]

end CC.Limb
