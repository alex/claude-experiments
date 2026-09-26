import ClaudeCrypto.Ppc.Basic

/-! # Lemmas about ppc64le register updates (not part of the TCB) -/

namespace CC.Ppc

theorem VRegs.get_set (g : VRegs) (r r' : VReg) (x : BitVec 128) :
    (g.set r x).get r' = if r' = r then x else g.get r' := by
  cases r <;> cases r' <;> rfl

theorem GRegs.get_set (g : GRegs) (r r' : GReg) (x : BitVec 64) :
    (g.set r x).get r' = if r' = r then x else g.get r' := by
  cases r <;> cases r' <;> rfl

namespace State

theorem getV_setV (s : State) (r r' : VReg) (x : BitVec 128) :
    (s.setV r x).getV r' = if r' = r then x else s.getV r' := VRegs.get_set _ _ _ _

theorem getV_setV_same (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).getV r = x := by
  rw [getV_setV, if_pos rfl]

theorem getV_setV_ne (s : State) (r r' : VReg) (x : BitVec 128) (h : r' ≠ r) :
    (s.setV r x).getV r' = s.getV r' := by
  rw [getV_setV, if_neg h]

theorem getG_setG (s : State) (r r' : GReg) (x : BitVec 64) :
    (s.setG r x).getG r' = if r' = r then x else s.getG r' := GRegs.get_set _ _ _ _

theorem getG_setG_same (s : State) (r : GReg) (x : BitVec 64) : (s.setG r x).getG r = x := by
  rw [getG_setG, if_pos rfl]

theorem getG_setG_ne (s : State) (r r' : GReg) (x : BitVec 64) (h : r' ≠ r) :
    (s.setG r x).getG r' = s.getG r' := by
  rw [getG_setG, if_neg h]

@[simp] theorem setV_g (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).g = s.g := rfl
@[simp] theorem setV_mem (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).mem = s.mem := rfl
@[simp] theorem setV_rd (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).rd = s.rd := rfl
@[simp] theorem setV_wr (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).wr = s.wr := rfl
@[simp] theorem setV_labels (s : State) (r : VReg) (x : BitVec 128) :
    (s.setV r x).labels = s.labels := rfl
@[simp] theorem setV_lr (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).lr = s.lr := rfl
@[simp] theorem setV_vsr (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).vsr = s.vsr := rfl
@[simp] theorem setV_cr1to7 (s : State) (r : VReg) (x : BitVec 128) :
    (s.setV r x).cr1to7 = s.cr1to7 := rfl
@[simp] theorem setV_getG (s : State) (r : VReg) (x : BitVec 128) (r' : GReg) :
    (s.setV r x).getG r' = s.getG r' := rfl

@[simp] theorem setG_v (s : State) (r : GReg) (x : BitVec 64) : (s.setG r x).v = s.v := rfl
@[simp] theorem setG_mem (s : State) (r : GReg) (x : BitVec 64) : (s.setG r x).mem = s.mem := rfl
@[simp] theorem setG_rd (s : State) (r : GReg) (x : BitVec 64) : (s.setG r x).rd = s.rd := rfl
@[simp] theorem setG_wr (s : State) (r : GReg) (x : BitVec 64) : (s.setG r x).wr = s.wr := rfl
@[simp] theorem setG_labels (s : State) (r : GReg) (x : BitVec 64) :
    (s.setG r x).labels = s.labels := rfl
@[simp] theorem setG_lr (s : State) (r : GReg) (x : BitVec 64) : (s.setG r x).lr = s.lr := rfl
@[simp] theorem setG_vsr (s : State) (r : GReg) (x : BitVec 64) : (s.setG r x).vsr = s.vsr := rfl
@[simp] theorem setG_cr1to7 (s : State) (r : GReg) (x : BitVec 64) :
    (s.setG r x).cr1to7 = s.cr1to7 := rfl
@[simp] theorem setG_getV (s : State) (r : GReg) (x : BitVec 64) (r' : VReg) :
    (s.setG r x).getV r' = s.getV r' := rfl

end State

end CC.Ppc
