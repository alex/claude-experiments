import ClaudeCrypto.X86.P384Wrap
import ClaudeCrypto.X86.Sym
import ClaudeCrypto.P384.MachineLemmas

/-!
# `cc_p384_verify_x86_bmi2` is correct

The whole emitted function (wrapper and compiled IR program) computes the ECDSA-P384
verification result of its inputs, restores the System V callee-saved registers and `rsp`,
and writes only its stack area.  The IR-level theorem `CC.P384.main_ok` is transported along
the verified compiler `CC.Limb.X86.sim`.
-/

namespace CC.X86.P384Wrap

open CC.P384

set_option hygiene false in
macro "agree_tac" : tactic => `(tactic|
  repeat (first
    | exact CC.Mem.Agree.refl _ _
    | refine CC.Mem.Agree.writeW ?_ _ _ (by
        first
        | (rw [CC.region_contains_add]; decide)
        | (rw [CC.region_contains_self]; decide))))

theorem prologue_exec (s : State) (F : Addr) (rest : List Region)
    (hrsp : s.gpr.rsp = F + 1840#64) (hwr : s.wr = ⟨F, 1840⟩ :: rest) :
    ∃ q, execBlock isa prologue s = some q ∧
      q.1.gpr = { s.gpr with rsp := F, r15 := F } ∧
      q.1.mem.readW (F + 1832#64) 64 = s.gpr.rbx ∧ q.1.mem.readW (F + 1824#64) 64 = s.gpr.rbp ∧
      q.1.mem.readW (F + 1816#64) 64 = s.gpr.r12 ∧ q.1.mem.readW (F + 1808#64) 64 = s.gpr.r13 ∧
      q.1.mem.readW (F + 1800#64) 64 = s.gpr.r14 ∧ q.1.mem.readW (F + 1792#64) 64 = s.gpr.r15 ∧
      Mem.Agree s.mem q.1.mem ⟨F, 1840⟩ ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  simp only [prologue, frameBytes]
  x86_sym [hrsp, hwr, CC.add_sub_lit]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  all_goals try x86_sym
  agree_tac

theorem epilogue_exec (s : State) (F : Addr) (rest : List Region)
    (hrsp : s.gpr.rsp = F) (hwr : s.wr = ⟨F, 1840⟩ :: rest)
    (r15 r14 r13 r12 rbp rbx : BitVec 64)
    (h15 : s.mem.readW (F + 1792#64) 64 = r15) (h14 : s.mem.readW (F + 1800#64) 64 = r14)
    (h13 : s.mem.readW (F + 1808#64) 64 = r13) (h12 : s.mem.readW (F + 1816#64) 64 = r12)
    (hbp : s.mem.readW (F + 1824#64) 64 = rbp) (hbx : s.mem.readW (F + 1832#64) 64 = rbx) :
    ∃ q, execBlock isa epilogue s = some q ∧
      q.1.gpr = { s.gpr with rsp := F + 1840#64, r15 := r15, r14 := r14, r13 := r13, r12 := r12,
                              rbp := rbp, rbx := rbx } ∧
      q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr := by
  simp only [epilogue, frameBytes]
  x86_sym [hrsp, hwr, h15, h14, h13, h12, hbp, hbx, BitVec.add_assoc]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- The IR state corresponding to the machine state after the prologue. -/
def irState (q : State) : Limb.State :=
  { r := fun v => q.gpr.get (Limb.X86.phys v), cf := none, sub := false, mem := q.mem, rd := q.rd, wr := q.wr,
    labels := q.labels }

/-- The statement of the IR-level theorem `CC.P384.main_ok` (assumed here, so that this file does
not depend on its proof). -/
def MainOk : Prop := ∀ s : Limb.State, MainPre s → WP Limb.isa main s (MainPost s)

/-- **Correctness, memory safety and ABI compliance of `cc_p384_verify_x86_bmi2`**, given the
IR-level theorem.  The function is called with the public key, digest and signature pointers in
`rdi`, `rsi`, `rdx`, and `rsp = F + 1840` where the 1840 bytes below the stack pointer (the six
pushes and the 1792-byte frame) are writable and disjoint from the inputs and the constants
table (which is at its label, in read-only memory).  Then the function terminates without
faulting, returns the ECDSA-P384 verification result in `rax`, restores `rsp` and the
callee-saved registers, and changes memory only in its stack area. -/
theorem correct_of (hmain : MainOk) (s : State) (F pk dg sg : Addr) (rest : List Region)
    (hrsp : s.gpr.rsp = F + 1840#64) (hwr : s.wr = ⟨F, 1840⟩ :: rest)
    (hrdi : s.gpr.rdi = pk) (hrsi : s.gpr.rsi = dg) (hrdx : s.gpr.rdx = sg)
    (hcs : Within s.rd (s.labels constLabel) constSize)
    (htab : ∀ j < constSize, s.mem (s.labels constLabel + BitVec.ofNat 64 j) = constTable[j]!)
    (hpk : Within (s.rd ++ s.wr) pk 96) (hdg : Within (s.rd ++ s.wr) dg 48)
    (hsg : Within (s.rd ++ s.wr) sg 96)
    (sepC : Mem.Sep F 1840 (s.labels constLabel) constSize)
    (sepPk : Mem.Sep F 1840 pk 96) (sepDg : Mem.Sep F 1840 dg 48) (sepSg : Mem.Sep F 1840 sg 96) :
    WP isa code s fun s' =>
      s'.gpr.rax = BitVec.ofNat 64 (if verifyMem s.mem pk dg sg then 1 else 0) ∧
      s'.gpr.rsp = s.gpr.rsp ∧ s'.gpr.rbx = s.gpr.rbx ∧ s'.gpr.rbp = s.gpr.rbp ∧
      s'.gpr.r12 = s.gpr.r12 ∧ s'.gpr.r13 = s.gpr.r13 ∧ s'.gpr.r14 = s.gpr.r14 ∧
      s'.gpr.r15 = s.gpr.r15 ∧ Mem.Agree s.mem s'.mem ⟨F, 1840⟩ ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨q1, hq1, hg1, sbx, sbp, s12, s13, s14, s15, hag1, hrd1, hwr1, hl1⟩ :=
    prologue_exec s F rest hrsp hwr
  have hcsz : constSize = 592 := rfl
  have hfsz : frameSize = 1784 := rfl
  -- the IR state after the prologue
  set si := irState q1.1 with hsi
  have hr : Limb.X86.Rel F si q1.1 :=
    ⟨fun _ => rfl, fun _ h => (by cases h), rfl, rfl, rfl, rfl, by rw [hg1]⟩
  have r14 : si.r 14 = F := by simp [hsi, irState, Limb.X86.phys, Regs.get, hg1]
  have r5 : si.r 5 = pk := by simp [hsi, irState, Limb.X86.phys, Regs.get, hg1, hrdi]
  have r4 : si.r 4 = dg := by simp [hsi, irState, Limb.X86.phys, Regs.get, hg1, hrsi]
  have r0 : si.r 0 = sg := by simp [hsi, irState, Limb.X86.phys, Regs.get, hg1, hrdx]
  have hmem1 : verifyMem q1.1.mem pk dg sg = verifyMem s.mem pk dg sg :=
    verifyMem_congr hag1 (by decide) pk dg sg sepPk sepDg sepSg
  have pre : MainPre si := by
    refine ⟨?_, ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Within q1.1.wr (si.r 14) frameSize
      rw [r14, hwr1, hwr]; exact within_head F 1840 _ rest (by decide) (by decide)
    · show Within q1.1.rd (q1.1.labels constLabel) constSize; rw [hrd1, hl1]; exact hcs
    · show q1.1.mem (q1.1.labels constLabel + BitVec.ofNat 64 j) = _
      rw [hl1, hag1.apply _ (by simpa using sepC.mono 0 j 1840 1 (by omega) (by omega) (by omega) (by omega)),
        htab j hj]
    · show Mem.Sep (si.r 14) frameSize (q1.1.labels constLabel) constSize
      rw [r14, hl1]; exact sep_shrink sepC (by decide) (by decide) (by decide)
    · show Within (q1.1.rd ++ q1.1.wr) (si.r 5) 96; rw [r5, hrd1, hwr1]; exact hpk
    · show Within (q1.1.rd ++ q1.1.wr) (si.r 4) 48; rw [r4, hrd1, hwr1]; exact hdg
    · show Within (q1.1.rd ++ q1.1.wr) (si.r 0) 96; rw [r0, hrd1, hwr1]; exact hsg
    · rw [r14, r5]; exact sep_shrink sepPk (by decide) (by decide) (by decide)
    · rw [r14, r4]; exact sep_shrink sepDg (by decide) (by decide) (by decide)
    · rw [r14, r0]; exact sep_shrink sepSg (by decide) (by decide) (by decide)
  have hw := (Limb.X86.sim F).wp (hmain si pre) q1.1 hr
  apply WP.seq
  refine WP.block_intro q1 hq1 ?_
  apply WP.seq
  refine WP.mono hw ?_
  rintro t ⟨s', hrel, hv, h14', hrd', hwr', hl', hag'⟩
  -- the saved registers are outside the frame
  have hagF : Mem.Agree q1.1.mem t.mem ⟨F, frameSize⟩ := by
    rw [hrel.mem]; have := hag'; rwa [r14] at this
  have saved : ∀ k : Nat, 1792 ≤ k → k + 8 ≤ 1840 →
      t.mem.readW (F + BitVec.ofNat 64 k) 64 = q1.1.mem.readW (F + BitVec.ofNat 64 k) 64 := by
    intro k hk1 hk2
    refine hagF.readW _ _ ?_
    have := Limb.sep_offsets F 0 k frameSize 8 (by left; omega) (by decide) (by omega) (by decide) (by decide)
    simpa using this
  have e15 := saved 1792 (by omega) (by omega); have e14 := saved 1800 (by omega) (by omega)
  have e13 := saved 1808 (by omega) (by omega); have e12 := saved 1816 (by omega) (by omega)
  have ebp := saved 1824 (by omega) (by omega); have ebx := saved 1832 (by omega) (by omega)
  have htwr : t.wr = ⟨F, 1840⟩ :: rest := by rw [hrel.wr, hwr', ← hwr, ← hwr1]; rfl
  obtain ⟨q4, hq4, hg4, hm4, hrd4, hwr4⟩ := epilogue_exec t F rest hrel.rsp htwr _ _ _ _ _ _
    (e15.trans s15) (e14.trans s14) (e13.trans s13) (e12.trans s12) (ebp.trans sbp) (ebx.trans sbx)
  refine WP.block_intro q4 hq4 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg4]
    show t.gpr.get (Limb.X86.phys 1) = _
    rw [hrel.regs 1, hv, r5, r4, r0]
    show BitVec.ofNat 64 (if verifyMem q1.1.mem pk dg sg then 1 else 0) = _
    rw [hmem1]
  · rw [hg4, hrsp]
  · rw [hg4]
  · rw [hg4]
  · rw [hg4]
  · rw [hg4]
  · rw [hg4]
  · rw [hg4]
  · rw [hm4]
    exact hag1.trans (hagF.widen (by decide))
  · rw [hrd4, hrel.rd, hrd', ← hrd1]; rfl
  · rw [hwr4, htwr, hwr]

end CC.X86.P384Wrap
