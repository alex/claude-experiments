import ClaudeCrypto.X86.Basic
import ClaudeCrypto.Common.MemLemmas

/-!
# Symbolic execution support for the x86-64 model

`x86_sym [facts]` rewrites `execBlock` of a concrete instruction list into the
resulting state, discharging permission checks and memory reads using the
supplied facts.
-/

namespace CC.X86

theorem bswap32_readW (m : Mem) (a : Addr) :
    bswap32 (m.readW a 32) = m a ++ m (a + 1) ++ m (a + 2) ++ m (a + 3) := by
  simp only [bswap32, Mem.readW, Mem.read]
  have e2 : a + 1 + 1 = a + 2 := by rw [BitVec.add_assoc]; rfl
  have e3 : a + 2 + 1 = a + 3 := by rw [BitVec.add_assoc]; rfl
  rw [e2, e3]
  generalize m a = b0; generalize m (a + 1) = b1; generalize m (a + 2) = b2; generalize m (a + 3) = b3
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

theorem setWidth_32_64_32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by simp
theorem setWidth_64_64 (x : BitVec 64) : x.setWidth 64 = x := by simp

end CC.X86

/-- Symbolically execute a straight-line x86 block. -/
syntax "x86_sym" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| x86_sym) => `(tactic| x86_sym [])
  | `(tactic| x86_sym [$ts,*]) => `(tactic|
    simp only [CC.execBlock, CC.X86.isa, CC.X86.exec, CC.X86.Instr.sz, CC.X86.execW, CC.X86.execAlu,
      CC.X86.execShift, CC.X86.readSrc, CC.X86.State.readW, CC.X86.State.writeW, CC.X86.State.loadW,
      CC.X86.State.storeW, CC.X86.State.ea, CC.X86.State.setReg, CC.X86.State.getReg, CC.X86.Regs.get,
      CC.X86.Regs.set, CC.X86.arithFlags, CC.X86.setFlags, CC.X86.addrs, CC.X86.srcAddrs,
      Option.map_some, Option.bind_some, Option.map, ite_true, ite_false,
      Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceLeDiff,
      Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, reduceIte,
      Int.reduceMul, Int.reduceAdd, Int.reduceMod, Int.reduceNeg, Nat.cast_ofNat,
      BitVec.ofInt_ofNat, BitVec.ofInt_natCast, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, BitVec.signExtend_eq,
      CC.X86.setWidth_32_64_32, CC.X86.setWidth_64_64, BitVec.add_zero, add_zero, BitVec.and_self,
      CC.inRegions_append, CC.inRegions_cons, CC.inRegions_nil, CC.region_contains_add,
      CC.region_contains_self, true_or, or_true, or_false, false_or,
      CC.Mem.readW_writeW_same_32, CC.Mem.readW_writeW_same_64, CC.Mem.readW_writeW_same_128, CC.Mem.readW_writeW_same_256, CC.Mem.readW_writeW_sep', CC.sep_add_add, CC.sep_self_add,
      CC.sep_add_self, CC.Mem.Sep, CC.addr_add_sub_cancel, CC.addr_sub_add_cancel, CC.addr_add_sub_add, CC.addr_sub_self, BitVec.reduceNeg, BitVec.reduceSignExtend, BitVec.reduceSub, BitVec.reduceAdd, BitVec.reduceToNat,
      and_true, true_and, decide_true, decide_false, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, $ts,*])
