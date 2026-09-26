import ClaudeCrypto.Ppc.Basic
import ClaudeCrypto.Common.MemLemmas

/-!
# Symbolic execution support for the ppc64le model

`ppc_sym [facts]` rewrites `execBlock` of a concrete instruction list into the
resulting state, discharging permission checks and register reads using the
supplied facts.  The vector operations (`vadduwm`, `vsldoi`, `vshasigmaw`, …)
are *not* unfolded: they are left for lemmas about `w4` (see
`Ppc/VecLemmas.lean`).  Permission checks are left in the form
`InRegions (s.rd ++ s.wr) a n` (resp. `InRegions s.wr a n`), to be
discharged by hypotheses of exactly that form.
-/

/-- Symbolically execute a straight-line ppc64le block. -/
syntax "ppc_sym" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ppc_sym) => `(tactic| ppc_sym [])
  | `(tactic| ppc_sym [$ts,*]) => `(tactic|
    simp only [CC.execBlock, CC.Ppc.isa, CC.Ppc.exec, CC.Ppc.addrs,
      CC.Ppc.State.getG, CC.Ppc.State.setG, CC.Ppc.State.getV, CC.Ppc.State.setV,
      CC.Ppc.State.ea, CC.Ppc.State.raOr0,
      CC.Ppc.GRegs.get, CC.Ppc.GRegs.set, CC.Ppc.VRegs.get, CC.Ppc.VRegs.set,
      Option.map_some, Option.bind_some, Option.map, ite_true, ite_false, reduceIte,
      Bool.true_eq_false, Bool.false_eq_true, List.length_cons, List.length_nil,
      Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceLeDiff,
      Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.cast_ofNat,
      BitVec.zero_add, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceMul,
      BitVec.reduceOfNat, BitVec.reduceOfInt, zero_add, add_zero,
      and_true, true_and, decide_true, decide_false, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.append_nil, $ts,*])
