import ClaudeCrypto.X86.SHA256.Scalar
import ClaudeCrypto.X86.Sym
import ClaudeCrypto.Spec.SHA256Lemmas

/-!
# Straight-line phases of the x86-64 scalar SHA-256 block function

Abstract execution lemmas for the message-load, finish, prologue and epilogue
code.  (The rounds are in `ScalarProof.lean`.)
-/

namespace CC.X86.SHA256Scalar

open CC.Spec.SHA256

set_option maxHeartbeats 4000000

/-- Prove `Mem.Agree m (m.writeW a₁ v₁ … .writeW aₙ vₙ) r` for writes inside `r`. -/
macro "agree_tac" : tactic => `(tactic|
  repeat (first
    | exact CC.Mem.Agree.refl _ _
    | refine CC.Mem.Agree.writeW ?_ _ _ (by
        first
        | (rw [CC.region_contains_add]; decide)
        | (rw [CC.region_contains_self]; decide))))

/-! ## Loading one message word -/

set_option hygiene false in
macro "load_tac" : tactic => `(tactic| (
  simp only [loadCode, slot, Nat.reduceMod, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_zero,
    Nat.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat] at hperm hx ⊢
  x86_sym [hrsp, hrsi, hwr, hperm, hx]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))

theorem load_exec (j : Nat) (hj : j < 16) (s : State) (sp p : Addr) (rest : List Region)
    (x : BitVec 32) (hrsp : s.gpr.rsp = sp) (hrsi : s.gpr.rsi = p) (hwr : s.wr = ⟨sp, 112⟩ :: rest)
    (hperm : InRegions s.rd (p + BitVec.ofNat 64 (4 * j)) 4)
    (hx : s.mem.readW (p + BitVec.ofNat 64 (4 * j)) 32 = x) :
    ∃ q, execBlock isa (loadCode j) s = some q ∧
      q.1.mem = s.mem.writeW (sp + BitVec.ofNat 64 (4 * (j % 16))) (bswap32 x) ∧
      q.1.gpr = s.gpr.set .rax ((bswap32 x).setWidth 64) ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧
      q.1.zf = s.zf ∧ q.1.cf = s.cf := by
  interval_cases j <;> load_tac

/-! ## Adding the working variables into the hash value -/

theorem finish_exec (s : State) (st sp p : Addr) (rest : List Region) (v : Vars) (H : List Word)
    (cnt : BitVec 64)
    (ha : s.gpr.r8 = v.a.setWidth 64) (hb : s.gpr.r9 = v.b.setWidth 64)
    (hc : s.gpr.r10 = v.c.setWidth 64) (hd : s.gpr.r11 = v.d.setWidth 64)
    (he : s.gpr.r12 = v.e.setWidth 64) (hf : s.gpr.r13 = v.f.setWidth 64)
    (hg : s.gpr.r14 = v.g.setWidth 64) (hh : s.gpr.r15 = v.h.setWidth 64)
    (hrdi : s.gpr.rdi = st) (hrsi : s.gpr.rsi = p) (hrdx : s.gpr.rdx = cnt)
    (hwr : s.wr = ⟨sp, 112⟩ :: ⟨st, 32⟩ :: rest)
    (hH : ∀ k < 8, s.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = H[k]!) :
    ∃ q, execBlock isa finish s = some q ∧
      q.1.gpr.r8 = (v.a + H[0]!).setWidth 64 ∧ q.1.gpr.r9 = (v.b + H[1]!).setWidth 64 ∧
      q.1.gpr.r10 = (v.c + H[2]!).setWidth 64 ∧ q.1.gpr.r11 = (v.d + H[3]!).setWidth 64 ∧
      q.1.gpr.r12 = (v.e + H[4]!).setWidth 64 ∧ q.1.gpr.r13 = (v.f + H[5]!).setWidth 64 ∧
      q.1.gpr.r14 = (v.g + H[6]!).setWidth 64 ∧ q.1.gpr.r15 = (v.h + H[7]!).setWidth 64 ∧
      q.1.mem.readW st 32 = v.a + H[0]! ∧
      q.1.mem.readW (st + 4#64) 32 = v.b + H[1]! ∧
      q.1.mem.readW (st + 8#64) 32 = v.c + H[2]! ∧
      q.1.mem.readW (st + 12#64) 32 = v.d + H[3]! ∧
      q.1.mem.readW (st + 16#64) 32 = v.e + H[4]! ∧
      q.1.mem.readW (st + 20#64) 32 = v.f + H[5]! ∧
      q.1.mem.readW (st + 24#64) 32 = v.g + H[6]! ∧
      q.1.mem.readW (st + 28#64) 32 = v.h + H[7]! ∧
      Mem.Agree s.mem q.1.mem ⟨st, 32⟩ ∧
      q.1.gpr.rsp = s.gpr.rsp ∧ q.1.gpr.rdi = st ∧ q.1.gpr.rsi = p + 64#64 ∧
      q.1.gpr.rdx = cnt - 1 ∧ q.1.zf = some (cnt - 1 == 0) ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr := by
  have h0 := hH 0 (by decide); have h1 := hH 1 (by decide); have h2 := hH 2 (by decide)
  have h3 := hH 3 (by decide); have h4 := hH 4 (by decide); have h5 := hH 5 (by decide)
  have h6 := hH 6 (by decide); have h7 := hH 7 (by decide)
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [finish, hReg, varReg, List.range, List.range.loop, List.map, List.flatten, Nat.reduceMod,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero, List.cons_append,
    List.nil_append, List.append_nil, List.append_eq]
  x86_sym [ha, hb, hc, hd, he, hf, hg, hh, hrdi, hrsi, hrdx, hwr, h0, h1, h2, h3, h4, h5, h6, h7]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals try x86_sym
  agree_tac

/-! ## Prologue and epilogue -/

theorem prologue_exec (s : State) (sp : Addr) (rest : List Region)
    (hrsp : s.gpr.rsp = sp + 112#64) (hwr : s.wr = ⟨sp, 112⟩ :: rest) :
    ∃ q, execBlock isa prologue s = some q ∧
      q.1.gpr = { s.gpr with rsp := sp } ∧
      q.1.mem.readW (sp + 104#64) 64 = s.gpr.rbx ∧ q.1.mem.readW (sp + 96#64) 64 = s.gpr.rbp ∧
      q.1.mem.readW (sp + 88#64) 64 = s.gpr.r12 ∧ q.1.mem.readW (sp + 80#64) 64 = s.gpr.r13 ∧
      q.1.mem.readW (sp + 72#64) 64 = s.gpr.r14 ∧ q.1.mem.readW (sp + 64#64) 64 = s.gpr.r15 ∧
      Mem.Agree s.mem q.1.mem ⟨sp, 112⟩ ∧
      q.1.zf = some (s.gpr.rdx == 0) ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr := by
  simp only [prologue]
  x86_sym [hrsp, hwr, CC.add_sub_lit]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  all_goals try x86_sym
  agree_tac

theorem epilogue_exec (s : State) (sp : Addr) (rest : List Region)
    (hrsp : s.gpr.rsp = sp) (hwr : s.wr = ⟨sp, 112⟩ :: rest)
    (r15 r14 r13 r12 rbp rbx : BitVec 64)
    (h15 : s.mem.readW (sp + 64#64) 64 = r15) (h14 : s.mem.readW (sp + 72#64) 64 = r14)
    (h13 : s.mem.readW (sp + 80#64) 64 = r13) (h12 : s.mem.readW (sp + 88#64) 64 = r12)
    (hbp : s.mem.readW (sp + 96#64) 64 = rbp) (hbx : s.mem.readW (sp + 104#64) 64 = rbx) :
    ∃ q, execBlock isa epilogue s = some q ∧
      q.1.gpr = { s.gpr with rsp := (sp + 112#64), r15 := r15, r14 := r14, r13 := r13, r12 := r12,
                              rbp := rbp, rbx := rbx } ∧
      q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr := by
  simp only [epilogue]
  x86_sym [hrsp, hwr, h15, h14, h13, h12, hbp, hbx, BitVec.add_assoc]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Loading the hash value -/

/-- The registers after loading the hash value `H` into `r8d..r15d`. -/
def loadH (r : Regs) (H : List Word) : Regs := { r with r8 := BitVec.setWidth 64 (H[0]!), r9 := BitVec.setWidth 64 (H[1]!), r10 := BitVec.setWidth 64 (H[2]!), r11 := BitVec.setWidth 64 (H[3]!), r12 := BitVec.setWidth 64 (H[4]!), r13 := BitVec.setWidth 64 (H[5]!), r14 := BitVec.setWidth 64 (H[6]!), r15 := BitVec.setWidth 64 (H[7]!) }

theorem loadState_exec (s : State) (st : Addr) (H : List Word) (hrdi : s.gpr.rdi = st)
    (hperm : ∀ k < 8, InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 (4 * k)) 4)
    (hH : ∀ k < 8, s.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = H[k]!) :
    ∃ q, execBlock isa loadState s = some q ∧
      q.1.gpr = loadH s.gpr H ∧
      q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr := by
  have h0 := hH 0 (by decide); have h1 := hH 1 (by decide); have h2 := hH 2 (by decide)
  have h3 := hH 3 (by decide); have h4 := hH 4 (by decide); have h5 := hH 5 (by decide)
  have h6 := hH 6 (by decide); have h7 := hH 7 (by decide)
  have p0 := hperm 0 (by decide); have p1 := hperm 1 (by decide); have p2 := hperm 2 (by decide)
  have p3 := hperm 3 (by decide); have p4 := hperm 4 (by decide); have p5 := hperm 5 (by decide)
  have p6 := hperm 6 (by decide); have p7 := hperm 7 (by decide)
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 p0 p1 p2 p3 p4 p5 p6 p7
  simp only [loadState, hReg, varReg, List.range, List.range.loop, List.map, Nat.reduceMod,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero]
  simp only [CC.execBlock, CC.X86.isa, CC.X86.exec, CC.X86.Instr.sz, CC.X86.execW, CC.X86.readSrc,
    CC.X86.State.readW, CC.X86.State.writeW, CC.X86.State.loadW, CC.X86.State.ea, CC.X86.State.setReg,
    CC.X86.State.getReg, CC.X86.Regs.get, CC.X86.Regs.set, CC.X86.addrs, CC.X86.srcAddrs,
    Option.map_some, Option.bind_some, Option.map, ite_true, Nat.reduceDiv, BitVec.ofInt_ofNat,
    BitVec.ofInt_natCast, BitVec.add_zero, hrdi, p0, p1, p2, p3, p4, p5, p6, p7, h0, h1, h2, h3, h4,
    h5, h6, h7, List.map_cons, List.map_nil, List.cons_append, List.nil_append, Nat.cast_ofNat,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff]
  exact ⟨_, rfl, by simp only [loadH, hrdi], rfl, rfl, rfl⟩

end CC.X86.SHA256Scalar
