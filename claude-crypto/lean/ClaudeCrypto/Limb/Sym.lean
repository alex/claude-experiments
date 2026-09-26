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

/-- Unfold the execution of a literal block of IR instructions. -/
macro "limb_sym" : tactic => `(tactic|
  simp only [CC.execBlock, CC.Limb.isa, CC.Limb.exec, CC.Limb.addrs, Option.map_some, Option.bind_some,
    CC.Limb.State.set_r, CC.Limb.State.set_cf, CC.Limb.State.set_sub, CC.Limb.State.set_mem,
    CC.Limb.State.set_rd, CC.Limb.State.set_wr, CC.Limb.State.set_labels, Function.update_self,
    Function.update_of_ne, ne_eq, reduceCtorEq, List.map_nil, List.nil_append, List.append_nil])

end CC.Limb
