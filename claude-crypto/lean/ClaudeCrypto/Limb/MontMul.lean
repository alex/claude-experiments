import ClaudeCrypto.Limb.MontRow

/-! # Montgomery multiplication: the six rounds -/

namespace CC.Limb

def montRounds (offA offB offN offMp : Nat) : List Instr :=
  ((List.range 6).map fun i => montRow offA offB offN offMp (0 + i)).flatten

section
variable (offA offB offN offMp : Nat) (s0 : State)

/-- The operands and constants, read from the initial state. -/
def opA : Nat := lsum (rowX s0 14 (fun j => offA + 8 * j)) 6
def opN : Nat := lsum (rowX s0 13 (fun j => offN + 8 * j)) 6
def digB (k : Nat) : Nat := (s0.mem.readW (s0.r 14 + BitVec.ofNat 64 (offB + 8 * k)) 64).toNat
def opMp : Nat := (s0.mem.readW (s0.r 13 + BitVec.ofNat 64 offMp) 64).toNat

structure MontInv (i : Nat) (s : State) : Prop where
  z : s.r 12 = 0
  e : s.r (rot i 7) = 0
  r13 : s.r 13 = s0.r 13
  r14 : s.r 14 = s0.r 14
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  labels : s.labels = s0.labels
  lt : acc s i 7 < 2 * opN offN s0
  eq : ∃ Q, 2 ^ (64 * i) * acc s i 7 = opA offA s0 * lsum (digB offB s0) i + Q * opN offN s0
end

theorem rot_wrap (i : Nat) : rot (i + 1) 7 = rot i 0 := by
  apply Fin.ext; simp only [rot_val]; omega

theorem lsum_rot_shift (s : State) (i : Nat) : acc s i 8 = (s.r (rot i 0)).toNat + 2 ^ 64 * acc s (i + 1) 7 := by
  unfold acc
  rw [lsum_shift]
  congr 2

set_option exponentiation.threshold 1000 in
theorem montRound_step (offA offB offN offMp : Nat) (s0 : State)
    (hA : opA offA s0 < opN offN s0) (hmp : (opMp offMp s0 * opN offN s0 + 1) % 2 ^ 64 = 0)
    (pA : ∀ k < 6, InRegions (s0.rd ++ s0.wr) (s0.r 14 + BitVec.ofNat 64 (offA + 8 * k)) 8)
    (pB : ∀ k < 6, InRegions (s0.rd ++ s0.wr) (s0.r 14 + BitVec.ofNat 64 (offB + 8 * k)) 8)
    (pN : ∀ k < 6, InRegions (s0.rd ++ s0.wr) (s0.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8)
    (pM : InRegions (s0.rd ++ s0.wr) (s0.r 13 + BitVec.ofNat 64 offMp) 8)
    (i : Nat) (hi : i < 6) (s : State) (h : MontInv offA offB offN s0 i s) :
    WP isa (.block (montRow offA offB offN offMp i)) s (MontInv offA offB offN s0 (i + 1)) := by
  have pre : RowPre offA offB offN offMp i s := by
    refine ⟨h.z, h.e, fun k hk => ?_, ?_, fun k hk => ?_, ?_⟩ <;>
      rw [h.rd, h.wr] <;> first | rw [h.r14] | rw [h.r13]
    · exact pA k hk
    · exact pB i hi
    · exact pN k hk
    · exact pM
  refine WP.mono (montRow_ok offA offB offN offMp i s pre) ?_
  rintro q ⟨hv, hz, h13, h14, hm, hrd, hwr, hl⟩
  -- rewrite the operands in terms of `s0`
  have eA : lsum (rowX s 14 (fun j => offA + 8 * j)) 6 = opA offA s0 := by
    unfold opA rowX; rw [h.mem, h.r14]
  have eN : lsum (rowX s 13 (fun j => offN + 8 * j)) 6 = opN offN s0 := by
    unfold opN rowX; rw [h.mem, h.r13]
  have eB : (s.mem.readW (s.r 14 + BitVec.ofNat 64 (offB + 8 * i)) 64).toNat = digB offB s0 i := by
    unfold digB; rw [h.mem, h.r14]
  have eM : (s.mem.readW (s.r 13 + BitVec.ofNat 64 offMp) 64).toNat = opMp offMp s0 := by
    unfold opMp; rw [h.mem, h.r13]
  rw [eA, eN, eB, eM] at hv
  set U := acc s i 7 + opA offA s0 * digB offB s0 i with hU
  set qd := Mont.qDigit (opMp offMp s0) U with hqd
  have hdvd : (U + qd * opN offN s0) % 2 ^ 64 = 0 := Mont.round_dvd _ _ _ hmp
  have h0 : (q.r (rot i 0)).toNat = 0 := by
    have := lsum_mod (fun k => (q.r (rot i k)).toNat) 7 0 (q.r (rot i 0)).isLt
    simp only [mul_zero, add_zero] at this
    rw [← this]; unfold acc at hv; rw [hv, hdvd]
  have hsh := lsum_rot_shift q i
  rw [h0, zero_add] at hsh
  have key : 2 ^ 64 * acc q (i + 1) 7 = U + qd * opN offN s0 := by rw [← hsh, hv]
  have hb : digB offB s0 i < 2 ^ 64 := BitVec.isLt _
  refine ⟨hz, ?_, h13.trans h.r13, h14.trans h.r14, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr,
    hl.trans h.labels, ?_, ?_⟩
  · rw [rot_wrap]; exact BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  · have := Mont.round_bound (opN offN s0) (acc s i 7) (opA offA s0) (digB offB s0 i) qd h.lt hA hb
      (Mont.qDigit_lt _ _)
    rw [← key, Nat.mul_div_cancel_left _ (by positivity)] at this
    exact this
  · obtain ⟨Q, hQ⟩ := h.eq
    refine ⟨Q + 2 ^ (64 * i) * qd, ?_⟩
    rw [lsum_succ, show 64 * (i + 1) = 64 * i + 64 by ring, pow_add, mul_assoc, key, hU]
    zify at hQ ⊢
    linear_combination hQ

def montInit : List Instr :=
  [.movi 12 0, .movi 1 0, .movi 2 0, .movi 3 0, .movi 4 0, .movi 5 0, .movi 6 0, .movi 7 0, .movi 8 0]

theorem montInit_exec (s : State) :
    ∃ q, execBlock isa montInit s = some q ∧ q.1.r 12 = 0 ∧ (∀ k, q.1.r (rot 0 k) = 0) ∧
      q.1.r 13 = s.r 13 ∧ q.1.r 14 = s.r 14 ∧ q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧
      q.1.labels = s.labels := by
  simp only [montInit]
  limb_sym
  refine ⟨_, rfl, rfl, fun k => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have : (rot 0 k).val < 9 ∧ 0 < (rot 0 k).val := by simp only [rot_val]; omega
  generalize rot 0 k = v at this
  obtain ⟨v, hv⟩ := v
  simp only at this
  obtain ⟨h1, h2⟩ := this
  interval_cases v <;> rfl

theorem montRounds_ok (offA offB offN offMp : Nat) (s0 : State)
    (hA : opA offA s0 < opN offN s0) (hmp : (opMp offMp s0 * opN offN s0 + 1) % 2 ^ 64 = 0)
    (pA : ∀ k < 6, InRegions (s0.rd ++ s0.wr) (s0.r 14 + BitVec.ofNat 64 (offA + 8 * k)) 8)
    (pB : ∀ k < 6, InRegions (s0.rd ++ s0.wr) (s0.r 14 + BitVec.ofNat 64 (offB + 8 * k)) 8)
    (pN : ∀ k < 6, InRegions (s0.rd ++ s0.wr) (s0.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8)
    (pM : InRegions (s0.rd ++ s0.wr) (s0.r 13 + BitVec.ofNat 64 offMp) 8) :
    WP isa (.block (montInit ++ montRounds offA offB offN offMp)) s0 (MontInv offA offB offN s0 6) := by
  apply WP.block_append
  obtain ⟨q, hq, hz, hr, h13, h14, hm, hrd, hwr, hl⟩ := montInit_exec s0
  refine WP.block_intro q hq ?_
  have hN : 0 < opN offN s0 := by
    rcases Nat.eq_zero_or_pos (opN offN s0) with h | h
    · rw [h] at hmp; norm_num at hmp
    · exact h
  have h0 : MontInv offA offB offN s0 0 q.1 := by
    have hacc : acc q.1 0 7 = 0 := by simp [acc, lsum, hr]
    refine ⟨hz, hr 7, h13, h14, hm, hrd, hwr, hl, by rw [hacc]; omega, ⟨0, by rw [hacc]; simp [lsum]⟩⟩
  have := WP.block_iter (M := isa) (montRow offA offB offN offMp) (MontInv offA offB offN s0) 0 6
    (fun i hi s hs => montRound_step offA offB offN offMp s0 hA hmp pA pB pN pM (0 + i) (by omega) s hs) q.1 h0
  simpa [montRounds] using this

end CC.Limb
