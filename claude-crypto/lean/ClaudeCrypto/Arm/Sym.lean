import ClaudeCrypto.Arm.Basic
import ClaudeCrypto.Common.MemLemmas

/-!
# Symbolic execution support for the AArch64 model

`arm_sym [facts]` rewrites `execBlock` of a concrete instruction list into the
resulting state, discharging permission checks and register reads using the
supplied facts.  The vector operations (`vadd32`, `rev32`, `sha256hash`, …)
are *not* unfolded: they are left for lemmas about `vec4` (see
`Arm/VecLemmas.lean`).  Permission checks are left in the form
`InRegions (s.rd ++ s.wr) a n` (resp. `InRegions s.wr a n`), to be
discharged by hypotheses of exactly that form.
-/

/-- Symbolically execute a straight-line AArch64 block. -/
syntax "arm_sym" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| arm_sym) => `(tactic| arm_sym [])
  | `(tactic| arm_sym [$ts,*]) => `(tactic|
    simp only [CC.execBlock, CC.Arm.isa, CC.Arm.exec, CC.Arm.addrs, CC.Arm.ldstAddrs,
      CC.Arm.State.getX, CC.Arm.State.setX, CC.Arm.State.getV, CC.Arm.State.setV,
      CC.Arm.State.loadW, CC.Arm.State.storeW, CC.Arm.State.ld1Regs, CC.Arm.State.st1Regs,
      CC.Arm.State.setNZCV, CC.Arm.condHolds,
      CC.Arm.XRegs.get, CC.Arm.XRegs.set, CC.Arm.VRegs.get, CC.Arm.VRegs.set,
      Option.map_some, Option.bind_some, Option.map, ite_true, ite_false, reduceIte,
      Bool.true_eq_false, Bool.false_eq_true, List.length_cons, List.length_nil,
      Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceLeDiff,
      Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.cast_ofNat,
      BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceMul, BitVec.reduceOfNat,
      BitVec.add_assoc, add_zero,
      CC.Mem.readW_writeW_same_32, CC.Mem.readW_writeW_same_64, CC.Mem.readW_writeW_same_128,
      and_true, true_and, decide_true, decide_false, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.append_nil, $ts,*])
