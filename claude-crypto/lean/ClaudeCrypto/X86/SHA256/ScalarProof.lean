import ClaudeCrypto.X86.SHA256.Scalar
import ClaudeCrypto.X86.Sym
import ClaudeCrypto.Spec.SHA256Lemmas

/-!
# Correctness proof of the x86-64 scalar SHA-256 block function
-/

namespace CC.X86.SHA256Scalar

open CC.Spec.SHA256

/-- Ghost state of the proof: the logical inputs of the function. -/
structure Ghost where
  /-- initial hash value (8 words) -/
  H : List Word
  /-- the message, `64 * n` bytes -/
  msg : List (BitVec 8)
  n : Nat
  /-- address of the hash value -/
  st : Addr
  /-- address of the message -/
  inp : Addr
  /-- base of the stack frame (the initial `rsp` minus 112) -/
  sp : Addr
  rd : List Region
  wr : List Region

namespace Ghost
def Hb (g : Ghost) (blk : Nat) : List Word := stateAfter g.H g.msg blk
def Mb (g : Ghost) (blk : Nat) : List Word := msgBlock g.msg blk
end Ghost

/-- Which message-schedule word is in slot `j` of the circular buffer before round `t`. -/
def slotIdx (t j : Nat) : Nat := if t ≤ 16 then j else t - 16 + (j + 16 - t % 16) % 16

def slotAddr (sp : Addr) (j : Nat) : Addr := sp + BitVec.ofNat 64 (4 * j)

/-- The invariant before round `t` of block `blk`; `mb` is the memory at the start of the block. -/
def RoundInv (g : Ghost) (blk t : Nat) (mb : Mem) (s : State) : Prop :=
  let v := varsAt (g.Hb blk) (g.Mb blk) t
  s.gpr.get (varReg t 0) = v.a.setWidth 64 ∧ s.gpr.get (varReg t 1) = v.b.setWidth 64 ∧
  s.gpr.get (varReg t 2) = v.c.setWidth 64 ∧ s.gpr.get (varReg t 3) = v.d.setWidth 64 ∧
  s.gpr.get (varReg t 4) = v.e.setWidth 64 ∧ s.gpr.get (varReg t 5) = v.f.setWidth 64 ∧
  s.gpr.get (varReg t 6) = v.g.setWidth 64 ∧ s.gpr.get (varReg t 7) = v.h.setWidth 64 ∧
  (∀ j < 16, s.mem.readW (slotAddr g.sp j) 32 = Wt (g.Mb blk) (slotIdx t j)) ∧
  s.gpr.rsp = g.sp ∧ s.gpr.rdi = g.st ∧ s.gpr.rsi = g.inp + BitVec.ofNat 64 (64 * blk) ∧
  s.gpr.rdx = BitVec.ofNat 64 (g.n - blk) ∧
  Mem.Agree mb s.mem ⟨g.sp, 64⟩ ∧ s.rd = g.rd ∧ s.wr = g.wr

/-! ## Arithmetic facts about the round computation -/

theorem ch_asm (e f g : Word) : (~~~e &&& g) + (f &&& e) = Ch e f g := by
  simp only [Ch]
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, hi,
      decide_true, Bool.true_and]
    cases e.getLsbD i <;> cases f.getLsbD i <;> cases g.getLsbD i <;> rfl
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
      BitVec.getLsbD_zero]
    cases e.getLsbD i <;> cases f.getLsbD i <;> cases g.getLsbD i <;> rfl

theorem maj_asm (a b c : Word) : ((b ^^^ c) &&& a ^^^ b &&& c) = Maj a b c := by
  simp only [Maj]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

theorem SIGMA1_asm (e : Word) : (e.rotateRight 6 ^^^ e.rotateRight 11 ^^^ e.rotateRight 25) = SIGMA1 e := rfl
theorem SIGMA0_asm (a : Word) : (a.rotateRight 2 ^^^ a.rotateRight 13 ^^^ a.rotateRight 22) = SIGMA0 a := rfl
theorem sigma0_asm (x : Word) : (x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> 3) = sigma0 x := rfl
theorem sigma1_asm (x : Word) : (x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> 10) = sigma1 x := rfl

/-! ## The circular schedule buffer -/

theorem slotAddr_sep (sp : Addr) (i j : Nat) (hi : i < 16) (hj : j < 16) (hij : i ≠ j) :
    Mem.Sep (slotAddr sp i) 4 (slotAddr sp j) 4 := by
  unfold slotAddr; rw [sep_add_add]
  unfold Mem.Sep
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem slots_write (m : Mem) (sp : Addr) (W : Nat → Word) (t : Nat) (ht : 16 ≤ t)
    (hslots : ∀ j < 16, m.readW (slotAddr sp j) 32 = W (slotIdx t j)) (a : Addr)
    (ha : slotAddr sp (t % 16) = a) (v : Word) (hv : v = W t) :
    ∀ j < 16, (m.writeW a v).readW (slotAddr sp j) 32 = W (slotIdx (t + 1) j) := by
  subst ha
  intro j hj
  by_cases hjt : j = t % 16
  · subst hjt; rw [Mem.readW_writeW_same _ _ _ (by decide) (by decide), hv]
    congr 1; unfold slotIdx; split_ifs <;> omega
  · rw [Mem.readW_writeW_sep _ _ _ _ _ (slotAddr_sep sp _ _ (by omega) hj (Ne.symm hjt)), hslots j hj]
    congr 1; unfold slotIdx; split_ifs <;> omega

theorem slots_same (m : Mem) (sp : Addr) (W : Nat → Word) (t : Nat) (ht : t < 16)
    (hslots : ∀ j < 16, m.readW (slotAddr sp j) 32 = W (slotIdx t j)) :
    ∀ j < 16, m.readW (slotAddr sp j) 32 = W (slotIdx (t + 1) j) := by
  intro j hj; rw [hslots j hj]; congr 1; unfold slotIdx; split_ifs <;> omega

/-- The schedule recurrence in terms of the slot contents before round `t`. -/
theorem Wt_slots (M : List Word) (t : Nat) (ht : 16 ≤ t) :
    Wt M t = Wt M (slotIdx t ((t + 16) % 16)) + sigma1 (Wt M (slotIdx t ((t + 14) % 16))) +
      Wt M (slotIdx t ((t + 9) % 16)) + sigma0 (Wt M (slotIdx t ((t + 1) % 16))) := by
  rw [Wt_ge M t ht]
  unfold slotIdx
  split_ifs with h
  · have : t = 16 := by omega
    subst this; simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reduceSub]; ac_rfl
  · have e1 : t - 16 + ((t + 16) % 16 + 16 - t % 16) % 16 = t - 16 := by omega
    have e2 : t - 16 + ((t + 14) % 16 + 16 - t % 16) % 16 = t - 2 := by omega
    have e3 : t - 16 + ((t + 9) % 16 + 16 - t % 16) % 16 = t - 7 := by omega
    have e4 : t - 16 + ((t + 1) % 16 + 16 - t % 16) % 16 = t - 15 := by omega
    rw [e1, e2, e3, e4]; ac_rfl

theorem add_ch_asm (x e f g : Word) : x + (~~~e &&& g) + (f &&& e) = x + Ch e f g := by
  rw [BitVec.add_assoc, ch_asm]

/-! ## One round -/

/-- The effect of round `t` on the machine state, in terms of abstract inputs. -/
def RoundPost (t : Nat) (v : Vars) (W : Nat → Word) (sp : Addr) (s s' : State) : Prop :=
  let v' := Spec.SHA256.round v K[t]! (W t)
  s'.gpr.get (varReg (t + 1) 0) = v'.a.setWidth 64 ∧ s'.gpr.get (varReg (t + 1) 1) = v'.b.setWidth 64 ∧
  s'.gpr.get (varReg (t + 1) 2) = v'.c.setWidth 64 ∧ s'.gpr.get (varReg (t + 1) 3) = v'.d.setWidth 64 ∧
  s'.gpr.get (varReg (t + 1) 4) = v'.e.setWidth 64 ∧ s'.gpr.get (varReg (t + 1) 5) = v'.f.setWidth 64 ∧
  s'.gpr.get (varReg (t + 1) 6) = v'.g.setWidth 64 ∧ s'.gpr.get (varReg (t + 1) 7) = v'.h.setWidth 64 ∧
  (∀ j < 16, s'.mem.readW (slotAddr sp j) 32 = W (slotIdx (t + 1) j)) ∧
  s'.gpr.rsp = sp ∧ s'.gpr.rdi = s.gpr.rdi ∧ s'.gpr.rsi = s.gpr.rsi ∧ s'.gpr.rdx = s.gpr.rdx ∧
  Mem.Agree s.mem s'.mem ⟨sp, 64⟩ ∧ s'.rd = s.rd ∧ s'.wr = s.wr

/-- Hypotheses of the abstract round lemma. -/
structure RoundPre (t : Nat) (v : Vars) (W : Nat → Word) (sp : Addr) (rest : List Region) (s : State) : Prop where
  ha : s.gpr.get (varReg t 0) = v.a.setWidth 64
  hb : s.gpr.get (varReg t 1) = v.b.setWidth 64
  hc : s.gpr.get (varReg t 2) = v.c.setWidth 64
  hd : s.gpr.get (varReg t 3) = v.d.setWidth 64
  he : s.gpr.get (varReg t 4) = v.e.setWidth 64
  hf : s.gpr.get (varReg t 5) = v.f.setWidth 64
  hg : s.gpr.get (varReg t 6) = v.g.setWidth 64
  hh : s.gpr.get (varReg t 7) = v.h.setWidth 64
  hslots : ∀ j < 16, s.mem.readW (slotAddr sp j) 32 = W (slotIdx t j)
  hW : 16 ≤ t → W t = W (slotIdx t ((t + 16) % 16)) + sigma1 (W (slotIdx t ((t + 14) % 16))) +
      W (slotIdx t ((t + 9) % 16)) + sigma0 (W (slotIdx t ((t + 1) % 16)))
  hrsp : s.gpr.rsp = sp
  hwr : s.wr = ⟨sp, 112⟩ :: rest

set_option hygiene false in
/-- Symbolically execute one round (common part). -/
macro "sha_round_exec" : tactic => `(tactic| (
  simp only [slotAddr, slotIdx, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
    Nat.reduceLeDiff, reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at w0 w1 w2 w3
  simp only [varReg, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, Regs.get] at ha hb hc hd he hf hg hh
  simp only [roundAll, schedCode, roundCode, varReg, slot, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, BitVec.ofInt_natCast, Int.reduceMod, Int.reduceMul, Nat.reduceMul,
    Nat.reduceLT, reduceIte, List.cons_append, List.nil_append]
  x86_sym [ha, hb, hc, hd, he, hf, hg, hh, hrsp, hwr, w0, w1, w2, w3]
  refine ⟨_, rfl, ?_⟩
  simp only [RoundPost, varReg, Regs.get, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub]
  simp only [sigma0_asm, sigma1_asm, SIGMA0_asm, SIGMA1_asm, maj_asm, add_ch_asm]))

set_option hygiene false in
/-- A round with a message-schedule update (`t ≥ 16`). -/
macro "sha_round_hi" : tactic => `(tactic| (
  sha_round_exec
  refine ⟨?_, rfl, rfl, rfl, ?_, rfl, rfl, rfl,
      slots_write _ _ W _ (by decide) hslots _
        (by simp only [slotAddr, Nat.reduceMod, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero]) _ ?_,
      trivial, trivial, trivial, trivial, Mem.Agree.writeW (Mem.Agree.refl _ _) _ _ ?_, trivial,
      hwr.symm⟩
  · rw [hW (by decide)]; simp only [Spec.SHA256.round, slotIdx, Nat.reduceMod, Nat.reduceAdd,
      Nat.reduceSub, Nat.reduceLeDiff, reduceIte]; refine congrArg _ ?_; ac_rfl
  · rw [hW (by decide)]; simp only [Spec.SHA256.round, slotIdx, Nat.reduceMod, Nat.reduceAdd,
      Nat.reduceSub, Nat.reduceLeDiff, reduceIte]; refine congrArg _ ?_; ac_rfl
  · rw [hW (by decide)]; simp only [slotIdx, Nat.reduceMod, Nat.reduceAdd,
      Nat.reduceSub, Nat.reduceLeDiff, reduceIte]; ac_rfl
  · first | (rw [region_contains_add]; decide) | (rw [region_contains_self]; decide)))

set_option hygiene false in
/-- A round without a message-schedule update (`t < 16`). -/
macro "sha_round_lo" : tactic => `(tactic| (
  sha_round_exec
  refine ⟨?_, rfl, rfl, rfl, ?_, rfl, rfl, rfl, slots_same _ _ W _ (by decide) hslots,
      trivial, trivial, trivial, trivial, Mem.Agree.refl _ _, trivial, hwr.symm⟩
  · simp only [Spec.SHA256.round]; refine congrArg _ ?_; ac_rfl
  · simp only [Spec.SHA256.round]; refine congrArg _ ?_; ac_rfl))

set_option maxHeartbeats 50000000

theorem round_exec_0 (t : Nat) (ht : t < 16) (v : Vars) (W : Nat → Word) (sp : Addr)
    (rest : List Region) (s : State) (hpre : RoundPre t v W sp rest s) :
    ∃ p, execBlock isa (roundAll t) s = some p ∧ RoundPost t v W sp s p.1 := by
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh, hslots, hW, hrsp, hwr⟩ := hpre
  have w0 := hslots ((t + 16) % 16) (Nat.mod_lt _ (by decide))
  have w1 := hslots ((t + 14) % 16) (Nat.mod_lt _ (by decide))
  have w2 := hslots ((t + 9) % 16) (Nat.mod_lt _ (by decide))
  have w3 := hslots ((t + 1) % 16) (Nat.mod_lt _ (by decide))
  interval_cases t <;> sha_round_lo

theorem round_exec_1 (t : Nat) (ht1 : 16 ≤ t) (ht : t < 32) (v : Vars) (W : Nat → Word) (sp : Addr)
    (rest : List Region) (s : State) (hpre : RoundPre t v W sp rest s) :
    ∃ p, execBlock isa (roundAll t) s = some p ∧ RoundPost t v W sp s p.1 := by
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh, hslots, hW, hrsp, hwr⟩ := hpre
  have w0 := hslots ((t + 16) % 16) (Nat.mod_lt _ (by decide))
  have w1 := hslots ((t + 14) % 16) (Nat.mod_lt _ (by decide))
  have w2 := hslots ((t + 9) % 16) (Nat.mod_lt _ (by decide))
  have w3 := hslots ((t + 1) % 16) (Nat.mod_lt _ (by decide))
  interval_cases t <;> sha_round_hi

theorem round_exec_2 (t : Nat) (ht1 : 32 ≤ t) (ht : t < 48) (v : Vars) (W : Nat → Word) (sp : Addr)
    (rest : List Region) (s : State) (hpre : RoundPre t v W sp rest s) :
    ∃ p, execBlock isa (roundAll t) s = some p ∧ RoundPost t v W sp s p.1 := by
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh, hslots, hW, hrsp, hwr⟩ := hpre
  have w0 := hslots ((t + 16) % 16) (Nat.mod_lt _ (by decide))
  have w1 := hslots ((t + 14) % 16) (Nat.mod_lt _ (by decide))
  have w2 := hslots ((t + 9) % 16) (Nat.mod_lt _ (by decide))
  have w3 := hslots ((t + 1) % 16) (Nat.mod_lt _ (by decide))
  interval_cases t <;> sha_round_hi

theorem round_exec_3 (t : Nat) (ht1 : 48 ≤ t) (ht : t < 64) (v : Vars) (W : Nat → Word) (sp : Addr)
    (rest : List Region) (s : State) (hpre : RoundPre t v W sp rest s) :
    ∃ p, execBlock isa (roundAll t) s = some p ∧ RoundPost t v W sp s p.1 := by
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh, hslots, hW, hrsp, hwr⟩ := hpre
  have w0 := hslots ((t + 16) % 16) (Nat.mod_lt _ (by decide))
  have w1 := hslots ((t + 14) % 16) (Nat.mod_lt _ (by decide))
  have w2 := hslots ((t + 9) % 16) (Nat.mod_lt _ (by decide))
  have w3 := hslots ((t + 1) % 16) (Nat.mod_lt _ (by decide))
  interval_cases t <;> sha_round_hi

theorem round_exec (t : Nat) (ht : t < 64) (v : Vars) (W : Nat → Word) (sp : Addr)
    (rest : List Region) (s : State) (hpre : RoundPre t v W sp rest s) :
    ∃ p, execBlock isa (roundAll t) s = some p ∧ RoundPost t v W sp s p.1 := by
  by_cases h1 : t < 16
  · exact round_exec_0 t h1 v W sp rest s hpre
  by_cases h2 : t < 32
  · exact round_exec_1 t (by omega) h2 v W sp rest s hpre
  by_cases h3 : t < 48
  · exact round_exec_2 t (by omega) h3 v W sp rest s hpre
  · exact round_exec_3 t (by omega) ht v W sp rest s hpre

end CC.X86.SHA256Scalar
