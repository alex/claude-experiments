import ClaudeCrypto.X86.SHA256.Avx2
import ClaudeCrypto.X86.Sym
import ClaudeCrypto.Spec.SHA256Lemmas

/-! # AVX2 SHA-256: one round (abstract lemma) -/

namespace CC.X86.SHA256Avx2

open CC.X86 CC.Spec.SHA256

theorem ch_asm (e f g : Word) : (f &&& e) + (~~~e &&& g) = Ch e f g := by
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

theorem maj_asm (a b c : Word) : ((b ^^^ c) &&& (a ^^^ b)) ^^^ b = Maj a b c := by
  simp only [Maj]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

theorem SIGMA1_asm (e : Word) : (e.rotateRight 6 ^^^ e.rotateRight 11 ^^^ e.rotateRight 25) = SIGMA1 e := rfl
theorem SIGMA0_asm (a : Word) : (a.rotateRight 13 ^^^ a.rotateRight 2 ^^^ a.rotateRight 22) = SIGMA0 a := by
  rw [SIGMA0, ROTR, ROTR, ROTR, BitVec.xor_comm (a.rotateRight 13)]

theorem sub_sigma (A S M : Word) : A + S + M - S = A + M := by abel

/-- Hypotheses of the round lemma, over abstract values. -/
structure RoundPre (L t : Nat) (v : Vars) (p wk : Word) (sp : Addr) (rest : List Region) (s : State) : Prop where
  ha : s.gpr.get (varReg t 0) = (v.a - p).setWidth 64
  hb : s.gpr.get (varReg t 1) = v.b.setWidth 64
  hc : s.gpr.get (varReg t 2) = v.c.setWidth 64
  hd : s.gpr.get (varReg t 3) = v.d.setWidth 64
  he : s.gpr.get (varReg t 4) = v.e.setWidth 64
  hf : s.gpr.get (varReg t 5) = v.f.setWidth 64
  hg : s.gpr.get (varReg t 6) = v.g.setWidth 64
  hh : s.gpr.get (varReg t 7) = v.h.setWidth 64
  hp : s.gpr.rbp = p.setWidth 64
  hz : s.gpr.get (tZ t) = (v.b ^^^ v.c).setWidth 64
  hwk : s.mem.readW (sp + BitVec.ofNat 64 (wkOff L t)) 32 = wk
  hrsp : s.gpr.rsp = sp
  hwr : s.wr = ⟨sp, 512⟩ :: rest

/-- The effect of a round. -/
def RoundPost (t : Nat) (v : Vars) (wk : Word) (s s' : State) : Prop :=
  let v' : Vars := ⟨v.h + SIGMA1 v.e + Ch v.e v.f v.g + wk + SIGMA0 v.a + Maj v.a v.b v.c, v.a, v.b, v.c,
    v.d + (v.h + SIGMA1 v.e + Ch v.e v.f v.g + wk), v.e, v.f, v.g⟩
  s'.gpr.get (varReg (t + 1) 0) = (v'.a - SIGMA0 v.a).setWidth 64 ∧
  s'.gpr.get (varReg (t + 1) 1) = v'.b.setWidth 64 ∧ s'.gpr.get (varReg (t + 1) 2) = v'.c.setWidth 64 ∧
  s'.gpr.get (varReg (t + 1) 3) = v'.d.setWidth 64 ∧ s'.gpr.get (varReg (t + 1) 4) = v'.e.setWidth 64 ∧
  s'.gpr.get (varReg (t + 1) 5) = v'.f.setWidth 64 ∧ s'.gpr.get (varReg (t + 1) 6) = v'.g.setWidth 64 ∧
  s'.gpr.get (varReg (t + 1) 7) = v'.h.setWidth 64 ∧
  s'.gpr.rbp = (SIGMA0 v.a).setWidth 64 ∧ s'.gpr.get (tZ (t + 1)) = (v'.b ^^^ v'.c).setWidth 64 ∧
  s'.gpr.rsp = s.gpr.rsp ∧ s'.gpr.rdi = s.gpr.rdi ∧ s'.gpr.rsi = s.gpr.rsi ∧ s'.gpr.rdx = s.gpr.rdx ∧
  s'.vec = s.vec ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.labels = s.labels

theorem add_ch (x e f g : Word) : x + (f &&& e) + (~~~e &&& g) = x + Ch e f g := by
  rw [← ch_asm, BitVec.add_assoc]

set_option hygiene false in
macro "avx_round_tac" : tactic => `(tactic| (
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh, hp, hz, hwk, hrsp, hwr⟩ := hpre
  simp only [varReg, stReg, tZ, tY, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, Regs.get, reduceIte,
    Nat.reduceEqDiff, wkOff, Nat.reduceMul, Nat.reduceDiv, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    at ha hb hc hd he hf hg hh hz hwk
  simp only [roundCode, varReg, stReg, tZ, tY, rspAt, wkOff, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Nat.reduceDiv, reduceIte, Nat.reduceEqDiff, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  x86_sym [ha, hb, hc, hd, he, hf, hg, hh, hp, hz, hwk, hrsp, hwr]
  refine ⟨_, rfl, ?_⟩
  simp only [RoundPost, varReg, stReg, tZ, tY, Regs.get, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub,
    reduceIte, Nat.reduceEqDiff]
  simp only [SIGMA0_asm, SIGMA1_asm, ch_asm, maj_asm, BitVec.sub_add_cancel, sub_sigma]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | trivial
    | rfl
    | exact hrsp.symm
    | exact hwr.symm
    | (refine congrArg _ ?_; ac_rfl)))

set_option maxHeartbeats 20000000

theorem round_exec_a (L t : Nat) (hL : L < 2) (ht : t < 16) (v : Vars) (p wk : Word) (sp : Addr)
    (rest : List Region) (s : State) (hpre : RoundPre L t v p wk sp rest s) :
    ∃ q, execBlock isa (roundCode L t) s = some q ∧ RoundPost t v wk s q.1 := by
  interval_cases L <;> interval_cases t <;> avx_round_tac

theorem round_exec_b (L t : Nat) (hL : L < 2) (ht1 : 16 ≤ t) (ht : t < 32) (v : Vars) (p wk : Word) (sp : Addr)
    (rest : List Region) (s : State) (hpre : RoundPre L t v p wk sp rest s) :
    ∃ q, execBlock isa (roundCode L t) s = some q ∧ RoundPost t v wk s q.1 := by
  interval_cases L <;> interval_cases t <;> avx_round_tac

theorem round_exec_c (L t : Nat) (hL : L < 2) (ht1 : 32 ≤ t) (ht : t < 48) (v : Vars) (p wk : Word) (sp : Addr)
    (rest : List Region) (s : State) (hpre : RoundPre L t v p wk sp rest s) :
    ∃ q, execBlock isa (roundCode L t) s = some q ∧ RoundPost t v wk s q.1 := by
  interval_cases L <;> interval_cases t <;> avx_round_tac

theorem round_exec_d (L t : Nat) (hL : L < 2) (ht1 : 48 ≤ t) (ht : t < 64) (v : Vars) (p wk : Word) (sp : Addr)
    (rest : List Region) (s : State) (hpre : RoundPre L t v p wk sp rest s) :
    ∃ q, execBlock isa (roundCode L t) s = some q ∧ RoundPost t v wk s q.1 := by
  interval_cases L <;> interval_cases t <;> avx_round_tac

theorem round_exec (L t : Nat) (hL : L < 2) (ht : t < 64) (v : Vars) (p wk : Word) (sp : Addr)
    (rest : List Region) (s : State) (hpre : RoundPre L t v p wk sp rest s) :
    ∃ q, execBlock isa (roundCode L t) s = some q ∧ RoundPost t v wk s q.1 := by
  by_cases h1 : t < 16
  · exact round_exec_a L t hL h1 v p wk sp rest s hpre
  by_cases h2 : t < 32
  · exact round_exec_b L t hL (by omega) h2 v p wk sp rest s hpre
  by_cases h3 : t < 48
  · exact round_exec_c L t hL (by omega) h3 v p wk sp rest s hpre
  · exact round_exec_d L t hL (by omega) ht v p wk sp rest s hpre

end CC.X86.SHA256Avx2
