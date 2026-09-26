import ClaudeCrypto.X86.SHA256.ShaNiLemmas

/-!
# Straight-line phases of the SHA-NI block function

Each lemma describes the state after running a phase, for arbitrary register
and memory contents, in terms of the instruction-level functions
(`sha256rnds2`, `padddX`, …) of the initial state.  All reasoning about what
the values mean is done elsewhere (`ShaNiLemmas.lean`, `ShaNiBlock.lean`).
The `xmm` writes are kept as `State.setX` chains, read back with `getX_setX`.
-/

namespace CC.X86

@[simp] theorem State.setX_gpr (s : State) (v : VReg) (x : BitVec 128) : (s.setX v x).gpr = s.gpr := rfl
@[simp] theorem State.setX_mem (s : State) (v : VReg) (x : BitVec 128) : (s.setX v x).mem = s.mem := rfl
@[simp] theorem State.setX_rd (s : State) (v : VReg) (x : BitVec 128) : (s.setX v x).rd = s.rd := rfl
@[simp] theorem State.setX_wr (s : State) (v : VReg) (x : BitVec 128) : (s.setX v x).wr = s.wr := rfl
@[simp] theorem State.setX_labels (s : State) (v : VReg) (x : BitVec 128) :
    (s.setX v x).labels = s.labels := rfl
@[simp] theorem State.setX_cf (s : State) (v : VReg) (x : BitVec 128) : (s.setX v x).cf = s.cf := rfl
@[simp] theorem State.setX_zf (s : State) (v : VReg) (x : BitVec 128) : (s.setX v x).zf = s.zf := rfl
@[simp] theorem State.setX_sf (s : State) (v : VReg) (x : BitVec 128) : (s.setX v x).sf = s.sf := rfl
@[simp] theorem State.setX_of (s : State) (v : VReg) (x : BitVec 128) : (s.setX v x).of = s.of := rfl

/-- Reading `xmm` from a state that shares its vector registers with `s`. -/
theorem State.getX_mk_vec (s : State) (g : Regs) (cf zf sf of : Option Bool) (m : Mem) (rd wr : List Region)
    (l : String → Addr) (w : VReg) :
    State.getX ⟨g, s.vec, cf, zf, sf, of, m, rd, wr, l⟩ w = s.getX w := rfl

theorem setWidth_append_128 (a b : BitVec 128) : (a ++ b).setWidth 128 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hi, decide_true, Bool.true_and, ite_true]

theorem State.getX_setX (s : State) (v w : VReg) (x : BitVec 128) :
    (s.setX v x).getX w = if w = v then x else s.getX w := by
  cases v <;> cases w <;> simp [State.setX, State.getX, VRegs.set, VRegs.get, setWidth_append_128]

end CC.X86

namespace CC.X86.SHA256ShaNi

open CC.X86

theorem wreg_eq_iff (a b : Nat) : wreg a = wreg b ↔ a % 4 = b % 4 := by
  unfold wreg
  constructor
  · intro h
    have ha := Nat.mod_lt a (show 4 > 0 by decide)
    have hb := Nat.mod_lt b (show 4 > 0 by decide)
    generalize a % 4 = x at *; generalize b % 4 = y at *
    interval_cases x <;> interval_cases y <;> simp_all
  · intro h; rw [h]

theorem wreg_ne (a b : Nat) (h : a % 4 ≠ b % 4) : wreg a ≠ wreg b := fun e => h ((wreg_eq_iff a b).mp e)

theorem wreg_ne_y0 (k : Nat) : wreg k ≠ .y0 := by unfold wreg; split <;> decide
theorem wreg_ne_y1 (k : Nat) : wreg k ≠ .y1 := by unfold wreg; split <;> decide
theorem wreg_ne_y2 (k : Nat) : wreg k ≠ .y2 := by unfold wreg; split <;> decide
theorem wreg_ne_y7 (k : Nat) : wreg k ≠ .y7 := by unfold wreg; split <;> decide
theorem wreg_ne_y8 (k : Nat) : wreg k ≠ .y8 := by unfold wreg; split <;> decide
theorem wreg_ne_y9 (k : Nat) : wreg k ≠ .y9 := by unfold wreg; split <;> decide
theorem wreg_ne_y10 (k : Nat) : wreg k ≠ .y10 := by unfold wreg; split <;> decide
theorem y0_ne_wreg (k : Nat) : VReg.y0 ≠ wreg k := (wreg_ne_y0 k).symm
theorem y1_ne_wreg (k : Nat) : VReg.y1 ≠ wreg k := (wreg_ne_y1 k).symm
theorem y2_ne_wreg (k : Nat) : VReg.y2 ≠ wreg k := (wreg_ne_y2 k).symm
theorem y7_ne_wreg (k : Nat) : VReg.y7 ≠ wreg k := (wreg_ne_y7 k).symm
theorem y8_ne_wreg (k : Nat) : VReg.y8 ≠ wreg k := (wreg_ne_y8 k).symm
theorem y9_ne_wreg (k : Nat) : VReg.y9 ≠ wreg k := (wreg_ne_y9 k).symm
theorem y10_ne_wreg (k : Nat) : VReg.y10 ≠ wreg k := (wreg_ne_y10 k).symm
theorem wreg_p_p1 (p : Nat) : wreg p ≠ wreg (p + 1) := wreg_ne _ _ (by omega)
theorem wreg_p1_p (p : Nat) : wreg (p + 1) ≠ wreg p := wreg_ne _ _ (by omega)
theorem wreg_p_p3 (p : Nat) : wreg p ≠ wreg (p + 3) := wreg_ne _ _ (by omega)
theorem wreg_p3_p (p : Nat) : wreg (p + 3) ≠ wreg p := wreg_ne _ _ (by omega)
theorem wreg_p1_p3 (p : Nat) : wreg (p + 1) ≠ wreg (p + 3) := wreg_ne _ _ (by omega)
theorem wreg_p3_p1 (p : Nat) : wreg (p + 3) ≠ wreg (p + 1) := wreg_ne _ _ (by omega)

/-- Symbolic execution for the SHA-NI code: `x86_sym` with the `xmm` lemmas. -/
macro "shani_sym" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  x86_sym [State.getX_setX, State.setX_gpr, State.setX_mem, State.setX_rd, State.setX_wr,
    State.setX_labels, State.setX_cf, State.setX_zf, State.setX_sf, State.setX_of, State.getX_mk_vec,
    reduceCtorEq, wreg_ne_y0, wreg_ne_y1, wreg_ne_y2, wreg_ne_y7, y0_ne_wreg, y1_ne_wreg, y2_ne_wreg,
    y7_ne_wreg, wreg_p_p1, wreg_p1_p, wreg_p_p3, wreg_p3_p, wreg_p1_p3, wreg_p3_p1, $ts,*])

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## Four rounds -/

theorem group_exec (p off : Nat) (fin m1 : Bool) (s : State)
    (hperm : InRegions (s.rd ++ s.wr) (s.labels kLabel + BitVec.ofNat 64 off) 16) :
    ∃ q, execBlock isa (groupCodeP p off fin m1) s = some q ∧
      q.1.getX .y2 = sha256rnds2 (s.getX .y2) (s.getX .y1)
        (padddX (s.mem.readW (s.labels kLabel + BitVec.ofNat 64 off) 128) (s.getX (wreg p))) ∧
      q.1.getX .y1 = sha256rnds2 (s.getX .y1)
        (sha256rnds2 (s.getX .y2) (s.getX .y1)
          (padddX (s.mem.readW (s.labels kLabel + BitVec.ofNat 64 off) 128) (s.getX (wreg p))))
        (pshufd128 (padddX (s.mem.readW (s.labels kLabel + BitVec.ofNat 64 off) 128) (s.getX (wreg p))) 14) ∧
      q.1.getX (wreg (p + 1)) = (if fin then
          sha256msg2 (padddX (s.getX (wreg (p + 1))) (palignr128 (s.getX (wreg p)) (s.getX (wreg (p + 3))) 4))
            (s.getX (wreg p))
        else s.getX (wreg (p + 1))) ∧
      q.1.getX (wreg (p + 3)) = (if m1 then sha256msg1 (s.getX (wreg (p + 3))) (s.getX (wreg p))
        else s.getX (wreg (p + 3))) ∧
      (∀ w, w ≠ .y0 → w ≠ .y1 → w ≠ .y2 → w ≠ .y7 → w ≠ wreg (p + 1) → w ≠ wreg (p + 3) →
        q.1.getX w = s.getX w) ∧
      q.1.gpr = s.gpr ∧ q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  cases fin <;> cases m1 <;>
  · simp only [groupCodeP, List.cons_append, List.nil_append, List.append_nil, ite_true, ite_false,
      Bool.false_eq_true, ripAt]
    shani_sym [hperm]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    all_goals first
      | (intro w h0 h1 h2 h7 ha hb; simp only [State.getX_setX, h0, h1, h2, h7, ha, hb, ite_false])
      | simp only [State.getX_setX, reduceCtorEq, wreg_ne_y0, wreg_ne_y1, wreg_ne_y2, wreg_ne_y7,
          y0_ne_wreg, y1_ne_wreg, y2_ne_wreg, y7_ne_wreg,
          wreg_p_p1, wreg_p1_p, wreg_p_p3, wreg_p3_p, wreg_p1_p3, wreg_p3_p1, ite_true, ite_false,
          Bool.false_eq_true]

/-! ## Loading the message block -/

/-! ## Loading the message block -/

theorem loadMsg_exec (s : State)
    (h0 : InRegions (s.rd ++ s.wr) s.gpr.rsi 16) (h1 : InRegions (s.rd ++ s.wr) (s.gpr.rsi + 16#64) 16)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr.rsi + 32#64) 16)
    (h3 : InRegions (s.rd ++ s.wr) (s.gpr.rsi + 48#64) 16) :
    ∃ q, execBlock isa loadMsg s = some q ∧
      q.1.getX .y3 = pshufb128 (s.mem.readW s.gpr.rsi 128) (s.getX .y8) ∧
      q.1.getX .y4 = pshufb128 (s.mem.readW (s.gpr.rsi + 16#64) 128) (s.getX .y8) ∧
      q.1.getX .y5 = pshufb128 (s.mem.readW (s.gpr.rsi + 32#64) 128) (s.getX .y8) ∧
      q.1.getX .y6 = pshufb128 (s.mem.readW (s.gpr.rsi + 48#64) 128) (s.getX .y8) ∧
      q.1.getX .y9 = s.getX .y1 ∧ q.1.getX .y10 = s.getX .y2 ∧
      (∀ w, w ≠ .y3 → w ≠ .y4 → w ≠ .y5 → w ≠ .y6 → w ≠ .y9 → w ≠ .y10 → q.1.getX w = s.getX w) ∧
      q.1.gpr = s.gpr ∧ q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  simp only [loadMsg]
  shani_sym [h0, h1, h2, h3]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro w a3 a4 a5 a6 a9 a10; simp only [State.getX_setX, a3, a4, a5, a6, a9, a10, ite_false])
    | simp only [State.getX_setX, reduceCtorEq, ite_true, ite_false, State.setX_gpr, State.setX_mem,
        State.setX_rd, State.setX_wr, State.setX_labels]

/-! ## Adding the saved hash value, advancing, counting down -/

theorem finish_exec (s : State) :
    ∃ q, execBlock isa finish s = some q ∧
      q.1.getX .y1 = padddX (s.getX .y1) (s.getX .y9) ∧ q.1.getX .y2 = padddX (s.getX .y2) (s.getX .y10) ∧
      (∀ w, w ≠ .y1 → w ≠ .y2 → q.1.getX w = s.getX w) ∧
      q.1.gpr = { s.gpr with rsi := s.gpr.rsi + 64#64, rdx := s.gpr.rdx - 1#64 } ∧
      q.1.zf = some (s.gpr.rdx - 1#64 == 0#64) ∧
      q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  simp only [finish]
  shani_sym []
  refine ⟨_, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals first
    | (intro w a1 a2; simp only [State.getX_mk_vec, State.getX_setX, a1, a2, ite_false])
    | simp only [State.getX_mk_vec, State.getX_setX, reduceCtorEq, ite_true, ite_false]

/-! ## Entry test, loading and storing the hash value -/

theorem entry_exec (s : State) :
    ∃ q, execBlock isa [.alu .test .q .rdx (.reg .rdx)] s = some q ∧ q.1.zf = some (s.gpr.rdx == 0#64) ∧
      q.1.gpr = s.gpr ∧ q.1.vec = s.vec ∧ q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧
      q.1.labels = s.labels := by
  x86_sym
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem loadState_exec (s : State)
    (h0 : InRegions (s.rd ++ s.wr) s.gpr.rdi 16) (h1 : InRegions (s.rd ++ s.wr) (s.gpr.rdi + 16#64) 16)
    (hb : InRegions (s.rd ++ s.wr) (s.labels bswapLabel) 16) :
    ∃ q, execBlock isa loadState s = some q ∧
      q.1.getX .y1 = punpckhqdqX (pshufd128 (s.mem.readW (s.gpr.rdi + 16#64) 128) 27)
        (pshufd128 (s.mem.readW s.gpr.rdi 128) 27) ∧
      q.1.getX .y2 = punpcklqdqX (pshufd128 (s.mem.readW (s.gpr.rdi + 16#64) 128) 27)
        (pshufd128 (s.mem.readW s.gpr.rdi 128) 27) ∧
      q.1.getX .y8 = s.mem.readW (s.labels bswapLabel) 128 ∧
      q.1.gpr = s.gpr ∧ q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  simp only [loadState, ripAt]
  shani_sym [h0, h1, hb]
  refine ⟨_, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩ <;>
    simp only [State.getX_setX, reduceCtorEq, ite_true, ite_false]

theorem storeState_exec (s : State)
    (h0 : InRegions s.wr s.gpr.rdi 16) (h1 : InRegions s.wr (s.gpr.rdi + 16#64) 16) :
    ∃ q, execBlock isa storeState s = some q ∧
      q.1.mem = (s.mem.writeW s.gpr.rdi (pshufd128 (punpckhqdqX (s.getX .y2) (s.getX .y1)) 27)).writeW
        (s.gpr.rdi + 16#64) (pshufd128 (punpcklqdqX (s.getX .y2) (s.getX .y1)) 27) ∧
      q.1.gpr = s.gpr ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr := by
  simp only [storeState]
  shani_sym [h0, h1]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

end CC.X86.SHA256ShaNi
