import ClaudeCrypto.Limb.Basic

/-! # Symbolic execution of IR blocks -/

namespace CC.Limb

theorem update_apply (f : Var → BitVec 64) (d v : Var) (x : BitVec 64) :
    Function.update f d x v = if v = d then x else f v := by
  by_cases h : v = d
  · subst h; simp
  · simp [h]

@[simp] theorem State.set_r (s : State) (d : Var) (x : BitVec 64) : (s.set d x).r = Function.update s.r d x := rfl
@[simp] theorem State.set_cf (s : State) (d : Var) (x : BitVec 64) : (s.set d x).cf = s.cf := rfl
@[simp] theorem State.set_sub (s : State) (d : Var) (x : BitVec 64) : (s.set d x).sub = s.sub := rfl
@[simp] theorem State.set_mem (s : State) (d : Var) (x : BitVec 64) : (s.set d x).mem = s.mem := rfl
@[simp] theorem State.set_rd (s : State) (d : Var) (x : BitVec 64) : (s.set d x).rd = s.rd := rfl
@[simp] theorem State.set_wr (s : State) (d : Var) (x : BitVec 64) : (s.set d x).wr = s.wr := rfl
@[simp] theorem State.set_labels (s : State) (d : Var) (x : BitVec 64) : (s.set d x).labels = s.labels := rfl

/-- Unfold the execution of a literal block of IR instructions (with extra simp lemmas, typically
the distinctness facts of the registers involved and permission facts). -/
syntax "limb_sym" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| limb_sym) => `(tactic| limb_sym [])
  | `(tactic| limb_sym [$ts,*]) => `(tactic|
    simp (config := { decide := true }) only [CC.execBlock, CC.Limb.isa, CC.Limb.exec, CC.Limb.addrs, CC.Limb.State.load,
      CC.Limb.State.store, Option.map_some, Option.bind_some, Option.map_none,
      CC.Limb.State.set_r, CC.Limb.State.set_cf, CC.Limb.State.set_sub, CC.Limb.State.set_mem,
      CC.Limb.State.set_rd, CC.Limb.State.set_wr, CC.Limb.State.set_labels, Function.update_self,
      Function.update_of_ne, ne_eq, not_false_eq_true, reduceCtorEq, List.map_nil, List.nil_append,
      List.append_nil, List.map_cons, List.cons_append, or_self, or_false, false_or, reduceIte,
      ite_true, ite_false, $ts,*])

end CC.Limb
