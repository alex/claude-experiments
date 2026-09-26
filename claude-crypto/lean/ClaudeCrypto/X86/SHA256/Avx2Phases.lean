import ClaudeCrypto.X86.SHA256.Avx2Lane

/-! # AVX2 SHA-256: straight-line phases -/

namespace CC.X86.SHA256Avx2

open BitVec CC.X86 CC.Spec.SHA256

set_option maxHeartbeats 4000000

/-- Prove `Mem.Agree m (m.writeW a₁ v₁ … .writeW aₙ vₙ) r` for writes inside `r`. -/
macro "agree_tac" : tactic => `(tactic|
  repeat (first
    | exact CC.Mem.Agree.refl _ _
    | refine CC.Mem.Agree.writeW ?_ _ _ (by
        first
        | (rw [CC.region_contains_add]; decide)
        | (rw [CC.region_contains_self]; decide))))

theorem laneInit_exec (H M : List Word) (s : State)
    (hr : ∀ k < 8, s.gpr.get (hReg k) = (H[k]!).setWidth 64) :
    ∃ q, execBlock isa laneInit s = some q ∧ RegsAt H M 0 q.1.gpr ∧
      q.1.gpr.rsp = s.gpr.rsp ∧ q.1.gpr.rdi = s.gpr.rdi ∧ q.1.gpr.rsi = s.gpr.rsi ∧
      q.1.gpr.rdx = s.gpr.rdx ∧ q.1.vec = s.vec ∧ q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧
      q.1.labels = s.labels := by
  have h0 := hr 0 (by decide); have h1 := hr 1 (by decide); have h2 := hr 2 (by decide)
  have h3 := hr 3 (by decide); have h4 := hr 4 (by decide); have h5 := hr 5 (by decide)
  have h6 := hr 6 (by decide); have h7 := hr 7 (by decide)
  simp only [hReg, varReg, stReg, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, Regs.get] at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [laneInit, tZ, varReg, stReg, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, reduceIte]
  x86_sym [h0, h1, h2, h3, h4, h5, h6, h7]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  constructor <;>
    simp only [varsAt_zero, initVars, pAt, reduceIte, varReg, stReg, tZ, Nat.reduceMod, Nat.reduceAdd,
      Nat.reduceSub, Regs.get, BitVec.sub_zero, sub_zero, BitVec.xor_self, h0, h1, h2, h3, h4, h5, h6, h7] <;>
    first | rfl | decide | skip

/-- The finishing code over abstract values. -/
theorem laneFinish_core (s : State) (st sp : Addr) (rest : List Region) (v : Vars) (p x0 x1 x2 x3 x4 x5 x6 x7 : Word)
    (ha : s.gpr.r8 = (v.a - p).setWidth 64) (hb : s.gpr.r9 = v.b.setWidth 64)
    (hc : s.gpr.r10 = v.c.setWidth 64) (hd : s.gpr.r11 = v.d.setWidth 64)
    (he : s.gpr.r12 = v.e.setWidth 64) (hf : s.gpr.r13 = v.f.setWidth 64)
    (hg : s.gpr.r14 = v.g.setWidth 64) (hh : s.gpr.r15 = v.h.setWidth 64)
    (hp : s.gpr.rbp = p.setWidth 64)
    (hrdi : s.gpr.rdi = st) (hwr : s.wr = ⟨sp, 560⟩ :: ⟨st, 32⟩ :: rest)
    (h0 : s.mem.readW st 32 = x0) (h1 : s.mem.readW (st + 4#64) 32 = x1)
    (h2 : s.mem.readW (st + 8#64) 32 = x2) (h3 : s.mem.readW (st + 12#64) 32 = x3)
    (h4 : s.mem.readW (st + 16#64) 32 = x4) (h5 : s.mem.readW (st + 20#64) 32 = x5)
    (h6 : s.mem.readW (st + 24#64) 32 = x6) (h7 : s.mem.readW (st + 28#64) 32 = x7) :
    ∃ q, execBlock isa laneFinish s = some q ∧
      q.1.gpr.r8 = (v.a + x0).setWidth 64 ∧ q.1.gpr.r9 = (v.b + x1).setWidth 64 ∧
      q.1.gpr.r10 = (v.c + x2).setWidth 64 ∧ q.1.gpr.r11 = (v.d + x3).setWidth 64 ∧
      q.1.gpr.r12 = (v.e + x4).setWidth 64 ∧ q.1.gpr.r13 = (v.f + x5).setWidth 64 ∧
      q.1.gpr.r14 = (v.g + x6).setWidth 64 ∧ q.1.gpr.r15 = (v.h + x7).setWidth 64 ∧
      q.1.mem.readW st 32 = v.a + x0 ∧
      q.1.mem.readW (st + 4#64) 32 = v.b + x1 ∧
      q.1.mem.readW (st + 8#64) 32 = v.c + x2 ∧
      q.1.mem.readW (st + 12#64) 32 = v.d + x3 ∧
      q.1.mem.readW (st + 16#64) 32 = v.e + x4 ∧
      q.1.mem.readW (st + 20#64) 32 = v.f + x5 ∧
      q.1.mem.readW (st + 24#64) 32 = v.g + x6 ∧
      q.1.mem.readW (st + 28#64) 32 = v.h + x7 ∧
      Mem.Agree s.mem q.1.mem ⟨st, 32⟩ ∧
      q.1.gpr.rsp = s.gpr.rsp ∧ q.1.gpr.rdi = s.gpr.rdi ∧ q.1.gpr.rsi = s.gpr.rsi ∧
      q.1.gpr.rdx = s.gpr.rdx ∧ q.1.vec = s.vec ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧
      q.1.labels = s.labels := by
  simp only [laneFinish, addH, hReg, varReg, stReg, List.range, List.range.loop, List.map, List.flatten,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero,
    List.cons_append, List.nil_append, List.append_nil, List.append_eq]
  x86_sym [ha, hb, hc, hd, he, hf, hg, hh, hp, hrdi, hwr, h0, h1, h2, h3, h4, h5, h6, h7,
    BitVec.sub_add_cancel]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals try x86_sym
  agree_tac

theorem laneFinish_exec (H M : List Word) (s : State) (st sp : Addr) (rest : List Region)
    (hr : RegsAt H M 64 s.gpr) (hrdi : s.gpr.rdi = st) (hwr : s.wr = ⟨sp, 560⟩ :: ⟨st, 32⟩ :: rest)
    (hH : ∀ k < 8, s.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = H[k]!) :
    ∃ q, execBlock isa laneFinish s = some q ∧
      (∀ k < 8, q.1.gpr.get (hReg k) = ((compress H M)[k]!).setWidth 64) ∧
      (∀ k < 8, q.1.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = (compress H M)[k]!) ∧
      Mem.Agree s.mem q.1.mem ⟨st, 32⟩ ∧
      q.1.gpr.rsp = s.gpr.rsp ∧ q.1.gpr.rdi = s.gpr.rdi ∧ q.1.gpr.rsi = s.gpr.rsi ∧
      q.1.gpr.rdx = s.gpr.rdx ∧ q.1.vec = s.vec ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧
      q.1.labels = s.labels := by
  have h0 := hH 0 (by decide); have h1 := hH 1 (by decide); have h2 := hH 2 (by decide)
  have h3 := hH 3 (by decide); have h4 := hH 4 (by decide); have h5 := hH 5 (by decide)
  have h6 := hH 6 (by decide); have h7 := hH 7 (by decide)
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7
  obtain ⟨ra, rb, rc, rd, re, rf, rg, rh, rp, -⟩ := hr
  simp only [varReg, stReg, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, Regs.get] at ra rb rc rd re rf rg rh
  obtain ⟨q, hq, g0, g1, g2, g3, g4, g5, g6, g7, m0, m1, m2, m3, m4, m5, m6, m7, hag, f1, f2, f3, f4, f5, f6,
      f7, f8⟩ :=
    laneFinish_core s st sp rest (varsAt H M 64) (pAt H M 64) _ _ _ _ _ _ _ _ ra rb rc rd re rf rg rh rp hrdi hwr
      h0 h1 h2 h3 h4 h5 h6 h7
  refine ⟨q, hq, ?_, ?_, hag, f1, f2, f3, f4, f5, f6, f7, f8⟩
  · intro k hk
    rw [compress_eq]
    interval_cases k
    · exact g0
    · exact g1
    · exact g2
    · exact g3
    · exact g4
    · exact g5
    · exact g6
    · exact g7
  · intro k hk
    rw [compress_eq]
    interval_cases k
    · simpa using m0
    · exact m1
    · exact m2
    · exact m3
    · exact m4
    · exact m5
    · exact m6
    · exact m7

/-! ## Prologue and epilogue -/

theorem prologue_exec (s : State) (sp : Addr) (rest : List Region)
    (hrsp : s.gpr.rsp = sp + 560#64) (hwr : s.wr = ⟨sp, 560⟩ :: rest) :
    ∃ q, execBlock isa prologue s = some q ∧
      q.1.gpr = { s.gpr with rsp := sp } ∧
      q.1.mem.readW (sp + 552#64) 64 = s.gpr.rbx ∧ q.1.mem.readW (sp + 544#64) 64 = s.gpr.rbp ∧
      q.1.mem.readW (sp + 536#64) 64 = s.gpr.r12 ∧ q.1.mem.readW (sp + 528#64) 64 = s.gpr.r13 ∧
      q.1.mem.readW (sp + 520#64) 64 = s.gpr.r14 ∧ q.1.mem.readW (sp + 512#64) 64 = s.gpr.r15 ∧
      Mem.Agree s.mem q.1.mem ⟨sp, 560⟩ ∧
      q.1.zf = some (s.gpr.rdx == 0) ∧ q.1.vec = s.vec ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧
      q.1.labels = s.labels := by
  simp only [prologue]
  x86_sym [hrsp, hwr, CC.add_sub_lit]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  all_goals try x86_sym
  agree_tac

theorem epilogue_exec (s : State) (sp : Addr) (rest : List Region)
    (hrsp : s.gpr.rsp = sp) (hwr : s.wr = ⟨sp, 560⟩ :: rest)
    (r15 r14 r13 r12 rbp rbx : BitVec 64)
    (h15 : s.mem.readW (sp + 512#64) 64 = r15) (h14 : s.mem.readW (sp + 520#64) 64 = r14)
    (h13 : s.mem.readW (sp + 528#64) 64 = r13) (h12 : s.mem.readW (sp + 536#64) 64 = r12)
    (hbp : s.mem.readW (sp + 544#64) 64 = rbp) (hbx : s.mem.readW (sp + 552#64) 64 = rbx) :
    ∃ q, execBlock isa epilogue s = some q ∧
      q.1.gpr = { s.gpr with rsp := (sp + 560#64), r15 := r15, r14 := r14, r13 := r13, r12 := r12,
                              rbp := rbp, rbx := rbx } ∧
      q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr := by
  simp only [epilogue]
  x86_sym [hrsp, hwr, h15, h14, h13, h12, hbp, hbx, BitVec.add_assoc]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Loading the masks and the hash value -/

/-- The registers after loading the hash value `H` into `r8d..r15d`. -/
def loadH (r : Regs) (H : List Word) : Regs := { r with r8 := BitVec.setWidth 64 (H[0]!), r9 := BitVec.setWidth 64 (H[1]!), r10 := BitVec.setWidth 64 (H[2]!), r11 := BitVec.setWidth 64 (H[3]!), r12 := BitVec.setWidth 64 (H[4]!), r13 := BitVec.setWidth 64 (H[5]!), r14 := BitVec.setWidth 64 (H[6]!), r15 := BitVec.setWidth 64 (H[7]!) }

theorem setup_exec (s : State) (st : Addr) (H : List Word) (hrdi : s.gpr.rdi = st)
    (hperm : ∀ k < 8, InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 (4 * k)) 4)
    (hH : ∀ k < 8, s.mem.readW (st + BitVec.ofNat 64 (4 * k)) 32 = H[k]!)
    (pb : InRegions (s.rd ++ s.wr) (s.labels bswapLabel) 32)
    (p1 : InRegions (s.rd ++ s.wr) (s.labels s00BALabel) 32)
    (p2 : InRegions (s.rd ++ s.wr) (s.labels sDC00Label) 32) :
    ∃ q, execBlock isa setup s = some q ∧
      q.1.gpr = loadH s.gpr H ∧ q.1.getV .y12 = s.mem.readW (s.labels bswapLabel) 256 ∧
      q.1.getV .y10 = s.mem.readW (s.labels s00BALabel) 256 ∧
      q.1.getV .y11 = s.mem.readW (s.labels sDC00Label) 256 ∧
      q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  have h0 := hH 0 (by decide); have h1 := hH 1 (by decide); have h2 := hH 2 (by decide)
  have h3 := hH 3 (by decide); have h4 := hH 4 (by decide); have h5 := hH 5 (by decide)
  have h6 := hH 6 (by decide); have h7 := hH 7 (by decide)
  have q0 := hperm 0 (by decide); have q1 := hperm 1 (by decide); have q2 := hperm 2 (by decide)
  have q3 := hperm 3 (by decide); have q4 := hperm 4 (by decide); have q5 := hperm 5 (by decide)
  have q6 := hperm 6 (by decide); have q7 := hperm 7 (by decide)
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 q0 q1 q2 q3 q4 q5 q6 q7
  simp only [setup, ripAt, hReg, varReg, stReg, List.range, List.range.loop, List.map, Nat.reduceMod,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero, List.cons_append,
    List.nil_append]
  simp only [CC.execBlock, CC.X86.isa, CC.X86.exec, CC.X86.Instr.sz, CC.X86.execW, CC.X86.execV,
    CC.X86.readSrc, CC.X86.State.readW, CC.X86.State.writeW, CC.X86.State.loadW, CC.X86.State.ea,
    CC.X86.State.setReg, CC.X86.State.setV, CC.X86.State.getV,
    CC.X86.State.getReg, CC.X86.Regs.get, CC.X86.Regs.set, CC.X86.addrs, CC.X86.srcAddrs,
    Option.map_some, Option.bind_some, Option.map, ite_true, Nat.reduceDiv, BitVec.ofInt_ofNat,
    BitVec.ofInt_natCast, BitVec.add_zero, hrdi, q0, q1, q2, q3, q4, q5, q6, q7, h0, h1, h2, h3, h4,
    h5, h6, h7, pb, p1, p2, List.map_cons, List.map_nil, List.cons_append, List.nil_append, Nat.cast_ofNat,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff]
  exact ⟨_, rfl, by simp only [loadH, hrdi], rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end CC.X86.SHA256Avx2
