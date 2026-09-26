import ClaudeCrypto.Limb.Chain

/-! # Modular addition and subtraction -/

namespace CC.Limb

def addTail : List Instr := [.movi (rot 6 6) 0, .adc (rot 6 6) 12]

/-- `D := A + B mod N` (operands at `r14 + off`, modulus at `r13 + offN`). -/
def addMod (offA offB offD offN : Nat) : Code Instr Cond :=
  .seq (.block ([.movi 12 0] ++ ldRow 14 offA ++ arRow false 14 offB)) (.seq (.block addTail) (montFinal offN offD))

/-- `D := A - B mod N`, computed as `A + (N - B)`. -/
def subMod (offA offB offD offN : Nat) : Code Instr Cond :=
  .seq (.block ([.movi 12 0] ++ ldRow 13 offN ++ arRow true 14 offB ++ arRow false 14 offA))
    (.seq (.block addTail) (montFinal offN offD))

theorem memX_mval (s : State) (base : Var) (off : Nat) :
    lsum (memX s base off) 6 = mval s.mem (s.r base + BitVec.ofNat 64 off) 6 := by
  unfold mval; apply lsum_congr; intro k _; unfold memX mlimb; rw [addr_add_ofNat']

theorem mod_of_lt2 (T N : Nat) (h : T < 2 * N) : (if T < N then T else T - N) = T % N := by
  split_ifs with h'
  · rw [Nat.mod_eq_of_lt h']
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Execution of `addTail`: the carry becomes the top limb. -/
theorem addTail_exec (s : State) (c : Bool) (hcf : s.cf = some c) (hsub : s.sub = false) (hz : s.r 12 = 0) :
    ∃ q, execBlock isa addTail s = some q ∧
      q.1.r = Function.update s.r (rot 6 6) ((BitVec.ofBool c).setWidth 64) ∧ q.1.mem = s.mem ∧
      q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  have n12 : rot 6 6 ≠ 12 := rot_ne_z _ _
  simp only [addTail]
  limb_sym [hcf, hsub, n12, hz]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl⟩
  funext v
  simp only [Function.update_idem]
  congr 1
  simp

/-- The common end of `addMod`/`subMod`: from limbs `T` in `rot 6 0..5` plus carry, reduce and store. -/
theorem addFinal_ok (offD offN : Nat) (s : State) (sI : State) (c : Bool)
    (hoffD : offD + 48 < 2 ^ 63) (hoffN : offN + 48 < 2 ^ 63)
    (hcf : s.cf = some c) (hsub : s.sub = false) (hz : s.r 12 = 0)
    (h13 : s.r 13 = sI.r 13) (h14 : s.r 14 = sI.r 14) (hm : s.mem = sI.mem) (hrd : s.rd = sI.rd)
    (hwr : s.wr = sI.wr) (hl : s.labels = sI.labels) (T : Nat)
    (hT : lsum (fun k => (s.r (rot 6 k)).toNat) 6 + 2 ^ (64 * 6) * c.toNat = T)
    (hT2 : T < 2 * mval sI.mem (sI.r 13 + BitVec.ofNat 64 offN) 6)
    (pN : ∀ k < 6, InRegions (sI.rd ++ sI.wr) (sI.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8)
    (pD : ∀ k < 6, InRegions sI.wr (sI.r 14 + BitVec.ofNat 64 (offD + 8 * k)) 8)
    (hsep : ∀ k < 6, Mem.Sep (sI.r 14 + BitVec.ofNat 64 offD) 48 (sI.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8) :
    WP isa (.seq (.block addTail) (montFinal offN offD)) s (fun q =>
      mval q.mem (sI.r 14 + BitVec.ofNat 64 offD) 6 = T % mval sI.mem (sI.r 13 + BitVec.ofNat 64 offN) 6 ∧
      Mem.Agree sI.mem q.mem ⟨sI.r 14 + BitVec.ofNat 64 offD, 48⟩ ∧ q.r 13 = sI.r 13 ∧ q.r 14 = sI.r 14 ∧
      q.rd = sI.rd ∧ q.wr = sI.wr ∧ q.labels = sI.labels) := by
  apply WP.seq
  obtain ⟨q, hq, qr, qm, qrd, qwr, ql⟩ := addTail_exec s c hcf hsub hz
  refine WP.block_intro q hq ?_
  have r : ∀ v, v ≠ rot 6 6 → q.1.r v = s.r v := fun v hv => by rw [qr, Function.update_of_ne hv]
  have q13 : q.1.r 13 = sI.r 13 := by rw [r 13 (rot_ne_13 _ _).symm, h13]
  have q14 : q.1.r 14 = sI.r 14 := by rw [r 14 (rot_ne_14 _ _).symm, h14]
  have hN : mval q.1.mem (nAddr offN q.1) 6 = mval sI.mem (sI.r 13 + BitVec.ofNat 64 offN) 6 := by
    rw [nAddr, q13, qm, hm]
  have hacc : acc q.1 6 7 = T := by
    unfold acc; rw [lsum_succ, ← hT]
    have : lsum (fun k => (q.1.r (rot 6 k)).toNat) 6 = lsum (fun k => (s.r (rot 6 k)).toNat) 6 :=
      lsum_congr _ _ _ (fun k hk => by rw [r _ (rot_ne_rot 6 k 6 (by omega) (by omega) (by omega))])
    rw [this, qr, Function.update_self]
    cases c <;> simp <;> ring
  refine WP.mono (montFinal_ok offN offD q.1 hoffD hoffN
    (fun k hk => by rw [qrd, qwr, hrd, hwr, q13]; exact pN k hk)
    (fun k hk => by rw [qwr, hwr, q14]; exact pD k hk)
    (fun k hk => by rw [dAddr, q14, q13]; exact hsep k hk)
    (by rw [r 12 (rot_ne_z _ _).symm, hz]) (by rw [hacc, hN]; exact hT2)) ?_
  rintro q2 ⟨hv, hag, h13', h14', hrd', hwr', hl'⟩
  rw [hacc, hN, mod_of_lt2 _ _ hT2, dAddr, q14] at hv
  rw [dAddr, q14, qm, hm] at hag
  exact ⟨hv, hag, h13'.trans q13, h14'.trans q14, hrd'.trans (qrd.trans hrd), hwr'.trans (qwr.trans hwr),
    hl'.trans (ql.trans hl)⟩

/-- Hypotheses shared by the field operations: offsets, permissions, separation. -/
structure OpPre (offA offB offD offN : Nat) (s : State) : Prop where
  hoffD : offD + 48 < 2 ^ 63
  hoffN : offN + 48 < 2 ^ 63
  pA : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.r 14 + BitVec.ofNat 64 (offA + 8 * k)) 8
  pB : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.r 14 + BitVec.ofNat 64 (offB + 8 * k)) 8
  pN : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8
  pD : ∀ k < 6, InRegions s.wr (s.r 14 + BitVec.ofNat 64 (offD + 8 * k)) 8
  sep : ∀ k < 6, Mem.Sep (s.r 14 + BitVec.ofNat 64 offD) 48 (s.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8

theorem addMod_ok (offA offB offD offN : Nat) (s : State) (h : OpPre offA offB offD offN s)
    (hA : mval s.mem (s.r 14 + BitVec.ofNat 64 offA) 6 < mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6)
    (hB : mval s.mem (s.r 14 + BitVec.ofNat 64 offB) 6 < mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6) :
    WP isa (addMod offA offB offD offN) s (fun q =>
      mval q.mem (s.r 14 + BitVec.ofNat 64 offD) 6 =
        (mval s.mem (s.r 14 + BitVec.ofNat 64 offA) 6 + mval s.mem (s.r 14 + BitVec.ofNat 64 offB) 6) %
          mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6 ∧
      Mem.Agree s.mem q.mem ⟨s.r 14 + BitVec.ofNat 64 offD, 48⟩ ∧ q.r 13 = s.r 13 ∧ q.r 14 = s.r 14 ∧
      q.rd = s.rd ∧ q.wr = s.wr ∧ q.labels = s.labels) := by
  unfold addMod
  apply WP.seq; apply WP.block_append; apply WP.block_append
  refine WP.block_intro (s.set 12 0, []) (by limb_sym) ?_
  set s1 := s.set 12 0 with hs1
  refine WP.mono (ldRow_ok 14 (by simp) offA s1 (fun k hk => h.pA k hk)) ?_
  intro s2 h2
  have r2 : ∀ v, (∀ k < 6, v ≠ rot 6 k) → v ≠ 10 → s2.r v = s1.r v := h2.frame.regs
  refine WP.mono (arRow_ok false 14 (by simp) offB s2 (fun k hk => by
    rw [h2.frame.rd, h2.frame.wr, r2 14 (fun j _ => (rot_ne_14 6 j).symm) (by decide)]; exact h.pB k hk)) ?_
  intro s3 h3
  obtain ⟨c, hcf, hsub, hrel⟩ := h3.rel (by decide)
  have r3 : ∀ v, (∀ k < 6, v ≠ rot 6 k) → v ≠ 10 → v ≠ 12 → s3.r v = s.r v := fun v a b e => by
    rw [h3.frame.regs v a b, r2 v a b, hs1, State.set_r, Function.update_of_ne e]
  have z3 : s3.r 12 = 0 := by
    rw [h3.frame.regs 12 (fun k _ => (rot_ne_z 6 k).symm) (by decide),
      r2 12 (fun k _ => (rot_ne_z 6 k).symm) (by decide), hs1, State.set_r, Function.update_self]
  have m3 : s3.mem = s.mem := by rw [h3.frame.mem, h2.frame.mem, hs1]; rfl
  have r14 : s3.r 14 = s.r 14 := r3 14 (fun k _ => (rot_ne_14 6 k).symm) (by decide) (by decide)
  have r13 : s3.r 13 = s.r 13 := r3 13 (fun k _ => (rot_ne_13 6 k).symm) (by decide) (by decide)
  -- the sum
  have hlim : ∀ k < 6, (s2.r (rot 6 k)).toNat = memX s 14 offA k := fun k hk => by
    rw [h2.lim k hk]; unfold memX; rw [hs1]; rfl
  have eX : lsum (memX s2 14 offB) 6 = mval s.mem (s.r 14 + BitVec.ofNat 64 offB) 6 := by
    rw [← memX_mval]; unfold memX
    rw [h2.frame.mem, r2 14 (fun j _ => (rot_ne_14 6 j).symm) (by decide), hs1]; rfl
  have eT : lsum (fun k => (s2.r (rot 6 k)).toNat) 6 = mval s.mem (s.r 14 + BitVec.ofNat 64 offA) 6 := by
    rw [lsum_congr _ _ _ hlim, memX_mval]
  unfold ArRel at hrel
  simp only [Bool.false_eq_true, ite_false, eX, eT] at hrel
  refine WP.mono (addFinal_ok offD offN s3 s c h.hoffD h.hoffN hcf hsub z3 r13 r14 m3
    (by rw [h3.frame.rd, h2.frame.rd, hs1]; rfl) (by rw [h3.frame.wr, h2.frame.wr, hs1]; rfl)
    (by rw [h3.frame.labels, h2.frame.labels, hs1]; rfl) _ hrel (by omega) h.pN h.pD h.sep) ?_
  exact fun q hq => hq

theorem subMod_ok (offA offB offD offN : Nat) (s : State) (h : OpPre offA offB offD offN s)
    (hA : mval s.mem (s.r 14 + BitVec.ofNat 64 offA) 6 < mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6)
    (hB : mval s.mem (s.r 14 + BitVec.ofNat 64 offB) 6 < mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6) :
    WP isa (subMod offA offB offD offN) s (fun q =>
      mval q.mem (s.r 14 + BitVec.ofNat 64 offD) 6 =
        (mval s.mem (s.r 14 + BitVec.ofNat 64 offA) 6 +
          (mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6 - mval s.mem (s.r 14 + BitVec.ofNat 64 offB) 6)) %
          mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6 ∧
      Mem.Agree s.mem q.mem ⟨s.r 14 + BitVec.ofNat 64 offD, 48⟩ ∧ q.r 13 = s.r 13 ∧ q.r 14 = s.r 14 ∧
      q.rd = s.rd ∧ q.wr = s.wr ∧ q.labels = s.labels) := by
  unfold subMod
  apply WP.seq; apply WP.block_append; apply WP.block_append; apply WP.block_append
  refine WP.block_intro (s.set 12 0, []) (by limb_sym) ?_
  set s1 := s.set 12 0 with hs1
  have e1 : ∀ v, v ≠ 12 → s1.r v = s.r v := fun v e => by rw [hs1, State.set_r, Function.update_of_ne e]
  refine WP.mono (ldRow_ok 13 (by simp) offN s1 (fun k hk => h.pN k hk)) ?_
  intro s2 h2
  have r2 : ∀ v, (∀ k < 6, v ≠ rot 6 k) → v ≠ 10 → s2.r v = s1.r v := h2.frame.regs
  have r14_2 : s2.r 14 = s.r 14 := by
    rw [r2 14 (fun j _ => (rot_ne_14 6 j).symm) (by decide), e1 14 (by decide)]
  refine WP.mono (arRow_ok true 14 (by simp) offB s2 (fun k hk => by
    rw [h2.frame.rd, h2.frame.wr, r14_2]; exact h.pB k hk)) ?_
  intro s3 h3
  obtain ⟨b, -, -, hrelB⟩ := h3.rel (by decide)
  have r3 : ∀ v, (∀ k < 6, v ≠ rot 6 k) → v ≠ 10 → s3.r v = s2.r v := h3.frame.regs
  have r14_3 : s3.r 14 = s.r 14 := by rw [r3 14 (fun j _ => (rot_ne_14 6 j).symm) (by decide), r14_2]
  refine WP.mono (arRow_ok false 14 (by simp) offA s3 (fun k hk => by
    rw [h3.frame.rd, h3.frame.wr, h2.frame.rd, h2.frame.wr, r14_3]; exact h.pA k hk)) ?_
  intro s4 h4
  obtain ⟨c, hcf, hsub, hrelA⟩ := h4.rel (by decide)
  have r4 : ∀ v, (∀ k < 6, v ≠ rot 6 k) → v ≠ 10 → v ≠ 12 → s4.r v = s.r v := fun v a b e => by
    rw [h4.frame.regs v a b, r3 v a b, r2 v a b, e1 v e]
  have z4 : s4.r 12 = 0 := by
    rw [h4.frame.regs 12 (fun k _ => (rot_ne_z 6 k).symm) (by decide),
      r3 12 (fun k _ => (rot_ne_z 6 k).symm) (by decide),
      r2 12 (fun k _ => (rot_ne_z 6 k).symm) (by decide), hs1, State.set_r, Function.update_self]
  have m2 : s2.mem = s.mem := by rw [h2.frame.mem, hs1]; rfl
  have m4 : s4.mem = s.mem := by rw [h4.frame.mem, h3.frame.mem, m2]
  -- the values
  have eN : lsum (fun k => (s2.r (rot 6 k)).toNat) 6 = mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6 := by
    rw [lsum_congr _ (memX s1 13 offN) _ (fun k hk => h2.lim k hk), memX_mval, e1 13 (by decide), hs1]; rfl
  have eB : lsum (memX s2 14 offB) 6 = mval s.mem (s.r 14 + BitVec.ofNat 64 offB) 6 := by
    rw [memX_mval, r14_2, m2]
  have eA : lsum (memX s3 14 offA) 6 = mval s.mem (s.r 14 + BitVec.ofNat 64 offA) 6 := by
    rw [memX_mval, r14_3, h3.frame.mem, m2]
  unfold ArRel at hrelB hrelA
  simp only [ite_true, eN, eB] at hrelB
  simp only [Bool.false_eq_true, ite_false, eA] at hrelA
  have hN := lsum_lt (mlimb s.mem (s.r 13 + BitVec.ofNat 64 offN)) 6 (fun k _ => BitVec.isLt _)
  have h3l := lsum_lt (fun k => (s3.r (rot 6 k)).toNat) 6 (fun k _ => BitVec.isLt _)
  have hb0 : b = false := by
    cases b
    · rfl
    · simp at hrelB; unfold mval at hA hB hrelB; omega
  subst hb0
  simp at hrelB
  have hT : lsum (fun k => (s4.r (rot 6 k)).toNat) 6 + 2 ^ (64 * 6) * c.toNat =
      mval s.mem (s.r 14 + BitVec.ofNat 64 offA) 6 +
        (mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6 - mval s.mem (s.r 14 + BitVec.ofNat 64 offB) 6) := by
    omega
  refine WP.mono (addFinal_ok offD offN s4 s c h.hoffD h.hoffN hcf hsub z4
    (r4 13 (fun k _ => (rot_ne_13 6 k).symm) (by decide) (by decide))
    (r4 14 (fun k _ => (rot_ne_14 6 k).symm) (by decide) (by decide)) m4
    (by rw [h4.frame.rd, h3.frame.rd, h2.frame.rd, hs1]; rfl)
    (by rw [h4.frame.wr, h3.frame.wr, h2.frame.wr, hs1]; rfl)
    (by rw [h4.frame.labels, h3.frame.labels, h2.frame.labels, hs1]; rfl) _ hT (by omega) h.pN h.pD h.sep) ?_
  exact fun q hq => hq

end CC.Limb
