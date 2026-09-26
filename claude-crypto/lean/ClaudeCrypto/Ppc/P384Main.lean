import ClaudeCrypto.Ppc.P384Wrap
import ClaudeCrypto.Ppc.Sym
import ClaudeCrypto.P384.MachineLemmas

/-!
# `cc_p384_verify_ppc64le` is correct

The whole emitted function (wrapper and compiled IR program) computes the ECDSA-P384
verification result of its inputs, returns it in `r3`, restores every register the ELFv2 ABI
requires a function to preserve (including the stack pointer `r1` and the link register), and
writes only its stack area.  The IR-level theorem `CC.P384.main_ok` is transported along the
verified compiler `CC.Limb.Ppc.sim`.
-/

namespace CC.Ppc.P384Wrap

open CC.P384

set_option linter.unusedSimpArgs false

set_option hygiene false in
macro "agree_tac" : tactic => `(tactic|
  repeat (first
    | exact CC.Mem.Agree.refl _ _
    | refine CC.Mem.Agree.writeW ?_ _ _ (by
        first
        | (rw [CC.region_contains_add]; decide)
        | (rw [CC.region_contains_self]; decide))))

/-- Reading back the saved registers from the stack area. -/
macro "stk_tac" : tactic => `(tactic|
  simp (disch := (simp only [CC.addr_add_sub_add, CC.addr_add_sub_cancel, CC.addr_sub_add_cancel,
      BitVec.reduceSub, BitVec.reduceNeg, BitVec.reduceToNat, Nat.reduceDiv, Nat.reduceLeDiff]))
    only [CC.Mem.readW_writeW_same_64, CC.Mem.readW_writeW_sep'])

theorem hF (F : Addr) : F + 1872#64 + 18446744073709549744#64 = F := by
  rw [BitVec.add_assoc]; simp

theorem prologue_exec (s : State) (F : Addr) (rest : List Region)
    (hr1 : s.getG .r1 = F + 1872#64) (hwr : s.wr = ⟨F, 1872⟩ :: rest) :
    ∃ q, execBlock isa prologue s = some q ∧
      q.1.g = ((((s.g.set .r1 F).set .r18 (F + 32#64)).set .r8 (s.getG .r3)).set .r7 (s.getG .r4)).set .r3
        (s.getG .r5) ∧
      q.1.mem.readW (F + 1824#64) 64 = s.getG .r14 ∧ q.1.mem.readW (F + 1832#64) 64 = s.getG .r15 ∧
      q.1.mem.readW (F + 1840#64) 64 = s.getG .r16 ∧ q.1.mem.readW (F + 1848#64) 64 = s.getG .r17 ∧
      q.1.mem.readW (F + 1856#64) 64 = s.getG .r18 ∧
      Mem.Agree s.mem q.1.mem ⟨F, 1872⟩ ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels ∧
      q.1.v = s.v ∧ q.1.vsr = s.vsr ∧ q.1.lr = s.lr ∧ q.1.cr1to7 = s.cr1to7 := by
  simp only [State.getG, GRegs.get] at hr1 ⊢
  simp only [prologue]
  ppc_sym [hr1, hwr, hF, CC.inRegions_cons, CC.region_contains_add, CC.region_contains_self,
    BitVec.reduceToNat, true_or, BitVec.or_self]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals try stk_tac
  agree_tac

theorem epilogue_exec (t : State) (F : Addr) (rest : List Region)
    (hr1 : t.getG .r1 = F) (hwr : t.wr = ⟨F, 1872⟩ :: rest)
    (a14 a15 a16 a17 a18 : BitVec 64)
    (h14 : t.mem.readW (F + 1824#64) 64 = a14) (h15 : t.mem.readW (F + 1832#64) 64 = a15)
    (h16 : t.mem.readW (F + 1840#64) 64 = a16) (h17 : t.mem.readW (F + 1848#64) 64 = a17)
    (h18 : t.mem.readW (F + 1856#64) 64 = a18) :
    ∃ q, execBlock isa epilogue t = some q ∧
      q.1.g = ((((((t.g.set .r3 (t.getG .r4)).set .r14 a14).set .r15 a15).set .r16 a16).set .r17 a17).set
        .r18 a18).set .r1 (F + 1872#64) ∧
      q.1.mem = t.mem ∧ q.1.rd = t.rd ∧ q.1.wr = t.wr ∧
      q.1.v = t.v ∧ q.1.vsr = t.vsr ∧ q.1.lr = t.lr ∧ q.1.cr1to7 = t.cr1to7 := by
  simp only [State.getG, GRegs.get] at hr1 ⊢
  simp only [epilogue]
  ppc_sym [hr1, hwr, h14, h15, h16, h17, h18, CC.inRegions_append, CC.inRegions_cons,
    CC.region_contains_add, CC.region_contains_self, BitVec.reduceToNat, true_or, or_true, BitVec.or_self]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem phys_nv (v : CC.Limb.Var) : (Limb.Ppc.phys v).nonvolatile = true →
    Limb.Ppc.phys v = .r14 ∨ Limb.Ppc.phys v = .r15 ∨ Limb.Ppc.phys v = .r16 ∨ Limb.Ppc.phys v = .r17 ∨
      Limb.Ppc.phys v = .r18 := by
  revert v; decide

/-- Agreement outside a sub-range of the stack area implies agreement outside the whole area. -/
theorem agree_sub {m m' : Mem} (F : Addr) (o L N : Nat) (h : Mem.Agree m m' ⟨F + BitVec.ofNat 64 o, L⟩)
    (hle : o + L ≤ N) (hN : N < 2 ^ 64) : Mem.Agree m m' ⟨F, N⟩ := by
  intro a ha
  apply h a
  intro hc; apply ha
  unfold Region.Contains at *; simp only at *
  have e : a - F = (a - (F + BitVec.ofNat 64 o)) + BitVec.ofNat 64 o := by abel
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The IR state corresponding to the machine state after the prologue. -/
def irState (q : State) : Limb.State :=
  { r := fun v => q.getG (Limb.Ppc.phys v), cf := none, sub := false, mem := q.mem, rd := q.rd, wr := q.wr,
    labels := q.labels }

/-- The statement of the IR-level theorem `CC.P384.main_ok` (assumed here, so that this file does
not depend on its proof). -/
def MainOk : Prop := ∀ s : Limb.State, MainPre s → WP Limb.isa main s (MainPost s)

set_option maxHeartbeats 1000000 in
/-- **Correctness, memory safety and ABI compliance of `cc_p384_verify_ppc64le`**, given the
IR-level theorem.  The function is called with the public key, digest and signature pointers in
`r3`, `r4`, `r5`, and `r1 = F + 1872` where the 1872 bytes below the stack pointer (the stack
frame: ELFv2 header, the IR frame and the save area of `r14`–`r18`) are writable and disjoint
from the inputs and the constants table (which is at its label, in read-only memory).  Then the
function terminates without faulting, returns the ECDSA-P384 verification result in `r3`,
preserves every register the ELFv2 ABI requires (`CalleeSaved`: `r1`, `r2`, `r13`–`r31`,
`v20`–`v31`, `f14`–`f31`, CR2–CR4 and the link register), and changes memory only in its stack
area. -/
theorem correct_of (hmain : MainOk) (s : State) (F pk dg sg : Addr) (rest : List Region)
    (hr1 : s.getG .r1 = F + 1872#64) (hwr : s.wr = ⟨F, 1872⟩ :: rest)
    (hr3 : s.getG .r3 = pk) (hr4 : s.getG .r4 = dg) (hr5 : s.getG .r5 = sg)
    (hcs : Within s.rd (s.labels constLabel) constSize)
    (htab : ∀ j < constSize, s.mem (s.labels constLabel + BitVec.ofNat 64 j) = constTable[j]!)
    (hpk : Within (s.rd ++ s.wr) pk 96) (hdg : Within (s.rd ++ s.wr) dg 48)
    (hsg : Within (s.rd ++ s.wr) sg 96)
    (sepC : Mem.Sep F 1872 (s.labels constLabel) constSize)
    (sepPk : Mem.Sep F 1872 pk 96) (sepDg : Mem.Sep F 1872 dg 48) (sepSg : Mem.Sep F 1872 sg 96) :
    WP isa code s fun s' =>
      s'.getG .r3 = BitVec.ofNat 64 (if verifyMem s.mem pk dg sg then 1 else 0) ∧
      CalleeSaved s s' ∧ Mem.Agree s.mem s'.mem ⟨F, 1872⟩ ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨q1, hq1, hg1, s14, s15, s16, s17, s18, hag1, hrd1, hwr1, hl1, hv1, hvsr1,
    hlr1, hcr1⟩ := prologue_exec s F rest hr1 hwr
  have hq1g : ∀ r, q1.1.getG r = (((((s.g.set .r1 F).set .r18 (F + 32#64)).set .r8 (s.getG .r3)).set .r7
      (s.getG .r4)).set .r3 (s.getG .r5)).get r := fun r => by rw [State.getG, hg1]
  have g1 : q1.1.getG .r1 = F := by rw [hq1g]; simp [GRegs.get_set]
  have g18 : q1.1.getG .r18 = F + 32#64 := by rw [hq1g]; simp [GRegs.get_set]
  have g8 : q1.1.getG .r8 = s.getG .r3 := by rw [hq1g]; simp [GRegs.get_set]
  have g7 : q1.1.getG .r7 = s.getG .r4 := by rw [hq1g]; simp [GRegs.get_set]
  have g3 : q1.1.getG .r3 = s.getG .r5 := by rw [hq1g]; simp [GRegs.get_set]
  have hcsz : constSize = 592 := rfl
  have hfsz : frameSize = 1784 := rfl
  -- the IR state after the prologue
  set si := irState q1.1 with hsi
  have hr : Limb.Ppc.Rel q1.1 si q1.1 :=
    ⟨fun _ => rfl, fun _ h => (by cases h), rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩
  have r14 : si.r 14 = F + BitVec.ofNat 64 32 := g18
  have r5 : si.r 5 = pk := g8.trans hr3
  have r4 : si.r 4 = dg := g7.trans hr4
  have r0 : si.r 0 = sg := g3.trans hr5
  have hmem1 : verifyMem q1.1.mem pk dg sg = verifyMem s.mem pk dg sg :=
    verifyMem_congr hag1 (by decide) pk dg sg sepPk sepDg sepSg
  have sub32 : ∀ {b : Addr} {n : Nat}, 0 < n → Mem.Sep F 1872 b n → Mem.Sep (F + BitVec.ofNat 64 32) frameSize b n :=
    fun hn h => by simpa using h.mono 32 0 frameSize _ (by decide) (by omega) (by decide) hn
  have pre : MainPre si := by
    refine ⟨?_, ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Within q1.1.wr (si.r 14) frameSize
      rw [r14, hwr1, hwr]
      exact ⟨⟨F, 1872⟩, List.mem_cons_self, by show 1872 < 2 ^ 64; norm_num,
        Region.contains_offset F 1872 32 frameSize (by decide) (by decide)⟩
    · show Within q1.1.rd (q1.1.labels constLabel) constSize; rw [hrd1, hl1]; exact hcs
    · show q1.1.mem (q1.1.labels constLabel + BitVec.ofNat 64 j) = _
      rw [hl1, hag1.apply _ (by simpa using sepC.mono 0 j 1872 1 (by omega) (by omega) (by omega) (by omega)),
        htab j hj]
    · show Mem.Sep (si.r 14) frameSize (q1.1.labels constLabel) constSize
      rw [r14, hl1]; exact sub32 (by decide) sepC
    · show Within (q1.1.rd ++ q1.1.wr) (si.r 5) 96; rw [r5, hrd1, hwr1]; exact hpk
    · show Within (q1.1.rd ++ q1.1.wr) (si.r 4) 48; rw [r4, hrd1, hwr1]; exact hdg
    · show Within (q1.1.rd ++ q1.1.wr) (si.r 0) 96; rw [r0, hrd1, hwr1]; exact hsg
    · rw [r14, r5]; exact sub32 (by decide) sepPk
    · rw [r14, r4]; exact sub32 (by decide) sepDg
    · rw [r14, r0]; exact sub32 (by decide) sepSg
  have hw := (Limb.Ppc.sim q1.1).wp (hmain si pre) q1.1 hr
  apply WP.seq
  refine WP.block_intro q1 hq1 ?_
  apply WP.seq
  refine WP.mono hw ?_
  rintro t ⟨s', hrel, hv, h14', hrd', hwr', hl', hag'⟩
  -- the saved registers are outside the IR frame
  have hagF : Mem.Agree q1.1.mem t.mem ⟨F + BitVec.ofNat 64 32, frameSize⟩ := by
    rw [hrel.mem]; have := hag'; rwa [r14] at this
  have saved : ∀ k : Nat, 1824 ≤ k → k + 8 ≤ 1872 →
      t.mem.readW (F + BitVec.ofNat 64 k) 64 = q1.1.mem.readW (F + BitVec.ofNat 64 k) 64 := by
    intro k hk1 hk2
    exact hagF.readW _ _ (Limb.sep_offsets F 32 k frameSize 8 (by left; omega) (by decide) (by omega)
      (by decide) (by decide))
  have e14 := saved 1824 (by omega) (by omega); have e15 := saved 1832 (by omega) (by omega)
  have e16 := saved 1840 (by omega) (by omega); have e17 := saved 1848 (by omega) (by omega)
  have e18 := saved 1856 (by omega) (by omega)
  have htwr : t.wr = ⟨F, 1872⟩ :: rest := by rw [hrel.wr, hwr', ← hwr, ← hwr1]; rfl
  have ht1 : t.getG .r1 = F := (hrel.frame .r1 (by decide) (by decide)).trans g1
  obtain ⟨q4, hq4, hg4, hm4, hrd4, hwr4, hv4, hvsr4, hlr4, hcr4⟩ :=
    epilogue_exec t F rest ht1 htwr _ _ _ _ _ (e14.trans s14) (e15.trans s15) (e16.trans s16)
      (e17.trans s17) (e18.trans s18)
  have hq4g : ∀ r, q4.1.getG r = (((((((t.g.set .r3 (t.getG .r4)).set .r14 (s.getG .r14)).set .r15
      (s.getG .r15)).set .r16 (s.getG .r16)).set .r17 (s.getG .r17)).set .r18 (s.getG .r18)).set .r1
      (F + 1872#64)).get r := fun r => by rw [State.getG, hg4]
  have f3 : q4.1.getG .r3 = t.getG .r4 := by rw [hq4g]; simp [GRegs.get_set]
  have f1 : q4.1.getG .r1 = F + 1872#64 := by rw [hq4g]; simp [GRegs.get_set]
  have f14 : q4.1.getG .r14 = s.getG .r14 := by rw [hq4g]; simp [GRegs.get_set]
  have f15 : q4.1.getG .r15 = s.getG .r15 := by rw [hq4g]; simp [GRegs.get_set]
  have f16 : q4.1.getG .r16 = s.getG .r16 := by rw [hq4g]; simp [GRegs.get_set]
  have f17 : q4.1.getG .r17 = s.getG .r17 := by rw [hq4g]; simp [GRegs.get_set]
  have f18 : q4.1.getG .r18 = s.getG .r18 := by rw [hq4g]; simp [GRegs.get_set]
  have fg : ∀ r, r ≠ .r1 → r ≠ .r3 → r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → r ≠ .r17 → r ≠ .r18 →
      q4.1.getG r = t.getG r := fun r h1 h3 h14 h15 h16 h17 h18 => by
    rw [hq4g]; simp [GRegs.get_set, h1, h3, h14, h15, h16, h17, h18]; rfl
  refine WP.block_intro q4 hq4 ⟨?_, ⟨fun r hr => ?_, fun r hr => ?_, fun m _ => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [f3]
    show t.getG (Limb.Ppc.phys 1) = _
    rw [hrel.regs 1, hv, r5, r4, r0]
    show BitVec.ofNat 64 (if verifyMem q1.1.mem pk dg sg then 1 else 0) = _
    rw [hmem1]
  · -- nonvolatile GPRs
    by_cases e1 : r = .r1
    · subst e1; rw [f1, hr1]
    by_cases e14 : r = .r14
    · subst e14; rw [f14]
    by_cases e15 : r = .r15
    · subst e15; rw [f15]
    by_cases e16 : r = .r16
    · subst e16; rw [f16]
    by_cases e17 : r = .r17
    · subst e17; rw [f17]
    by_cases e18 : r = .r18
    · subst e18; rw [f18]
    have e3 : r ≠ .r3 := by rintro rfl; cases hr
    have e7 : r ≠ .r7 := by rintro rfl; cases hr
    have e8 : r ≠ .r8 := by rintro rfl; cases hr
    have hnp : ∀ v, Limb.Ppc.phys v ≠ r := by
      intro v hv'
      have := phys_nv v
      rw [hv'] at this
      rcases this hr with h | h | h | h | h
      exacts [e14 h, e15 h, e16 h, e17 h, e18 h]
    have hns : r ≠ Limb.Ppc.scratch := by rintro rfl; cases hr
    rw [fg r e1 e3 e14 e15 e16 e17 e18, hrel.frame r hnp hns, hq1g]
    simp [GRegs.get_set, e1, e3, e7, e8, e18]; rfl
  · rw [show q4.1.getV r = t.getV r from congrArg (VRegs.get · r) hv4, show t.getV r = q1.1.getV r from
      congrArg (VRegs.get · r) hrel.v, show q1.1.getV r = s.getV r from congrArg (VRegs.get · r) hv1]
  · rw [hvsr4, hrel.vsr, hvsr1]
  · rw [hcr4, hrel.cr1to7, hcr1]
  · rw [hlr4, hrel.lr, hlr1]
  · rw [hm4]
    exact hag1.trans (agree_sub F 32 frameSize 1872 hagF (by decide) (by decide))
  · rw [hrd4, hrel.rd, hrd', ← hrd1]; rfl
  · rw [hwr4, htwr, hwr]

end CC.Ppc.P384Wrap
