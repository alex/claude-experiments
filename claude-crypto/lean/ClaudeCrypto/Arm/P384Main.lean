import ClaudeCrypto.Arm.P384Wrap
import ClaudeCrypto.Arm.StateLemmas
import ClaudeCrypto.P384.MachineLemmas

/-!
# `cc_p384_verify_aarch64` is correct

The whole emitted function (wrapper and compiled IR program) computes the ECDSA-P384
verification result of its inputs, restores `SP`, preserves every register the IR code does
not own (in particular all AAPCS64 callee-saved registers) and writes only its stack frame.
The IR-level theorem `CC.P384.main_ok` is transported along the verified compiler
`CC.Limb.Arm.sim`.
-/

namespace CC.Arm.P384Wrap

open CC.P384

/-- The state after the prologue. -/
def afterPro (s : State) : State :=
  ({ ((s.setX .x5 (s.getX .x0)).setX .x4 (s.getX .x1)).setX .x0 (s.getX .x2) with
      sp := s.sp - BitVec.ofNat 64 frameBytes }).setX .x14 (s.sp - BitVec.ofNat 64 frameBytes)

theorem getX_withSp (s : State) (v : BitVec 64) (r : XReg) : ({ s with sp := v } : State).getX r = s.getX r := rfl

theorem prologue_exec (s : State) : execBlock isa prologue s = some (afterPro s, []) := rfl

theorem afterPro_getX (s : State) (r : XReg) (h0 : r ≠ .x0) (h4 : r ≠ .x4) (h5 : r ≠ .x5) (h14 : r ≠ .x14) :
    (afterPro s).getX r = s.getX r := by
  simp only [afterPro, State.getX_setX, getX_withSp, h0, h4, h5, h14, ite_false]

/-- The IR state corresponding to the machine state after the prologue. -/
def irState (q : State) : Limb.State :=
  { r := fun v => q.getX (Limb.Arm.phys v), cf := none, sub := false, mem := q.mem, rd := q.rd, wr := q.wr,
    labels := q.labels }

/-- The statement of the IR-level theorem `CC.P384.main_ok` (assumed here, so that this file does
not depend on its proof). -/
def MainOk : Prop := ∀ s : Limb.State, MainPre s → WP Limb.isa main s (MainPost s)

/-- **Correctness, memory safety and ABI compliance of `cc_p384_verify_aarch64`**, given the
IR-level theorem.  The function is called with the public key, digest and signature pointers in
`x0`, `x1`, `x2`, and `SP = F + 1792` where the 1792 bytes below the stack pointer are writable
and disjoint from the inputs and the constants table (at its label, readable).  Then it
terminates without faulting, returns the ECDSA-P384 verification result in `x0`, restores `SP`,
leaves every general-purpose register other than `x0`–`x14` and `x16` (in particular `x18`–`x30`)
and all vector registers unchanged (so it satisfies the AAPCS64 `CalleeSaved` contract), and
changes memory only in its stack frame. -/
theorem correct_of (hmain : MainOk) (s : State) (F pk dg sg : Addr)
    (hsp : s.sp = F + 1792#64) (hstk : Within s.wr F 1792)
    (hx0 : s.getX .x0 = pk) (hx1 : s.getX .x1 = dg) (hx2 : s.getX .x2 = sg)
    (hcs : Within s.rd (s.labels constLabel) constSize)
    (htab : ∀ j < constSize, s.mem (s.labels constLabel + BitVec.ofNat 64 j) = constTable[j]!)
    (hpk : Within (s.rd ++ s.wr) pk 96) (hdg : Within (s.rd ++ s.wr) dg 48)
    (hsg : Within (s.rd ++ s.wr) sg 96)
    (sepC : Mem.Sep F 1792 (s.labels constLabel) constSize)
    (sepPk : Mem.Sep F 1792 pk 96) (sepDg : Mem.Sep F 1792 dg 48) (sepSg : Mem.Sep F 1792 sg 96) :
    WP isa code s fun s' =>
      s'.getX .x0 = BitVec.ofNat 64 (if verifyMem s.mem pk dg sg then 1 else 0) ∧
      s'.sp = s.sp ∧ (∀ r, (∀ v, Limb.Arm.phys v ≠ r) → r ≠ .x16 → s'.getX r = s.getX r) ∧
      s'.v = s.v ∧ CalleeSaved s s' ∧
      Mem.Agree s.mem s'.mem ⟨F, 1792⟩ ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  set q := afterPro s with hq
  have hF : s.sp - BitVec.ofNat 64 frameBytes = F := by
    rw [hsp]; show F + BitVec.ofNat 64 1792 - BitVec.ofNat 64 1792 = F; exact BitVec.add_sub_cancel _ _
  have qsp : q.sp = F := by rw [hq, afterPro]; exact hF
  have qmem : q.mem = s.mem := rfl
  set si := irState q with hsi
  have hr : Limb.Arm.Rel q si q :=
    ⟨fun _ => rfl, fun _ h => (by cases h), rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩
  have r14 : si.r 14 = F := by
    show q.getX .x14 = F; rw [hq, afterPro, State.getX_setX_same, hF]
  have r5 : si.r 5 = pk := by
    show q.getX .x5 = pk
    rw [hq, afterPro, State.getX_setX_ne _ _ _ _ (by decide), getX_withSp, State.getX_setX_ne _ _ _ _ (by decide), State.getX_setX_ne _ _ _ _ (by decide), State.getX_setX_same, hx0]
  have r4 : si.r 4 = dg := by
    show q.getX .x4 = dg
    rw [hq, afterPro, State.getX_setX_ne _ _ _ _ (by decide), getX_withSp, State.getX_setX_ne _ _ _ _ (by decide), State.getX_setX_same, hx1]
  have r0 : si.r 0 = sg := by
    show q.getX .x0 = sg
    rw [hq, afterPro, State.getX_setX_ne _ _ _ _ (by decide), getX_withSp, State.getX_setX_same, hx2]
  have pre : MainPre si := by
    refine ⟨?_, ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [r14]; exact hstk.shrink (by decide)
    · exact hcs
    · exact htab j hj
    · rw [r14]; exact sep_shrink sepC (by decide) (by decide) (by decide)
    · rw [r5]; exact hpk
    · rw [r4]; exact hdg
    · rw [r0]; exact hsg
    · rw [r14, r5]; exact sep_shrink sepPk (by decide) (by decide) (by decide)
    · rw [r14, r4]; exact sep_shrink sepDg (by decide) (by decide) (by decide)
    · rw [r14, r0]; exact sep_shrink sepSg (by decide) (by decide) (by decide)
  have hw := (Limb.Arm.sim q).wp (hmain si pre) q hr
  apply WP.seq
  refine WP.block_intro (q, []) (prologue_exec s) ?_
  apply WP.seq
  refine WP.mono hw ?_
  rintro t ⟨s', hrel, hv, h14', hrd', hwr', hl', hag'⟩
  have hagF : Mem.Agree s.mem t.mem ⟨F, frameSize⟩ := by
    rw [hrel.mem]; have := hag'; rwa [r14] at this
  -- the frame of the IR code: registers it does not own keep their values from the start
  have keep : ∀ r, (∀ v, Limb.Arm.phys v ≠ r) → r ≠ .x16 → t.getX r = s.getX r := by
    intro r hr1 hr2
    rw [hrel.frame r hr1 hr2]
    exact afterPro_getX s r (Ne.symm (hr1 0)) (Ne.symm (hr1 4)) (Ne.symm (hr1 5)) (Ne.symm (hr1 14))
  have ne0 : ∀ r : XReg, (∀ v, Limb.Arm.phys v ≠ r) → r ≠ .x0 := fun r hr1 h => hr1 0 (by rw [h]; rfl)
  have hres : t.getX .x1 = BitVec.ofNat 64 (if verifyMem s.mem pk dg sg then 1 else 0) := by
    have := hrel.regs 1
    rw [hv, r5, r4, r0] at this
    exact this
  have hsp' : t.sp + BitVec.ofNat 64 frameBytes = s.sp := by
    rw [hrel.sp, qsp, hsp]; rfl
  have hv' : t.v = s.v := by rw [hrel.v]; rfl
  have keep' : ∀ r, (∀ v, Limb.Arm.phys v ≠ r) → r ≠ .x16 →
      ({ t.setX .x0 (t.getX .x1) with sp := t.sp + BitVec.ofNat 64 frameBytes } : State).getX r = s.getX r :=
    fun r hr1 hr2 => by rw [getX_withSp, State.getX_setX_ne _ _ _ _ (ne0 r hr1)]; exact keep r hr1 hr2
  refine WP.block_intro ({ t.setX .x0 (t.getX .x1) with sp := t.sp + BitVec.ofNat 64 frameBytes }, [])
    rfl ⟨?_, hsp', keep', hv', ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [getX_withSp, State.getX_setX_same, hres]
  · exact ⟨keep' .x19 (by decide) (by decide), keep' .x20 (by decide) (by decide),
      keep' .x21 (by decide) (by decide), keep' .x22 (by decide) (by decide),
      keep' .x23 (by decide) (by decide), keep' .x24 (by decide) (by decide),
      keep' .x25 (by decide) (by decide), keep' .x26 (by decide) (by decide),
      keep' .x27 (by decide) (by decide), keep' .x28 (by decide) (by decide),
      keep' .x29 (by decide) (by decide), keep' .x30 (by decide) (by decide), hsp',
      by rw [State.setX_v, hv'], by rw [State.setX_v, hv'], by rw [State.setX_v, hv'], by rw [State.setX_v, hv'],
      by rw [State.setX_v, hv'], by rw [State.setX_v, hv'], by rw [State.setX_v, hv'], by rw [State.setX_v, hv']⟩
  · exact hagF.widen (by decide)
  · dsimp only; rw [State.setX_rd, hrel.rd, hrd']; rfl
  · dsimp only; rw [State.setX_wr, hrel.wr, hwr']; rfl

end CC.Arm.P384Wrap
