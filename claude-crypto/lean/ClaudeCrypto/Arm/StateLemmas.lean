import ClaudeCrypto.Arm.Basic

/-! # Lemmas about AArch64 register updates (not part of the TCB) -/

namespace CC.Arm

theorem VRegs.get_set (g : VRegs) (r r' : VReg) (x : BitVec 128) :
    (g.set r x).get r' = if r' = r then x else g.get r' := by
  cases r <;> cases r' <;> rfl

theorem XRegs.get_set (g : XRegs) (r r' : XReg) (x : BitVec 64) :
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

theorem getX_setX (s : State) (r r' : XReg) (x : BitVec 64) :
    (s.setX r x).getX r' = if r' = r then x else s.getX r' := XRegs.get_set _ _ _ _

theorem getX_setX_same (s : State) (r : XReg) (x : BitVec 64) : (s.setX r x).getX r = x := by
  rw [getX_setX, if_pos rfl]

theorem getX_setX_ne (s : State) (r r' : XReg) (x : BitVec 64) (h : r' ≠ r) :
    (s.setX r x).getX r' = s.getX r' := by
  rw [getX_setX, if_neg h]

@[simp] theorem setV_x (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).x = s.x := rfl
@[simp] theorem setV_sp (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).sp = s.sp := rfl
@[simp] theorem setV_mem (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).mem = s.mem := rfl
@[simp] theorem setV_rd (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).rd = s.rd := rfl
@[simp] theorem setV_wr (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).wr = s.wr := rfl
@[simp] theorem setV_labels (s : State) (r : VReg) (x : BitVec 128) :
    (s.setV r x).labels = s.labels := rfl
@[simp] theorem setV_getX (s : State) (r : VReg) (x : BitVec 128) (r' : XReg) :
    (s.setV r x).getX r' = s.getX r' := rfl

@[simp] theorem setX_v (s : State) (r : XReg) (x : BitVec 64) : (s.setX r x).v = s.v := rfl
@[simp] theorem setX_sp (s : State) (r : XReg) (x : BitVec 64) : (s.setX r x).sp = s.sp := rfl
@[simp] theorem setX_mem (s : State) (r : XReg) (x : BitVec 64) : (s.setX r x).mem = s.mem := rfl
@[simp] theorem setX_rd (s : State) (r : XReg) (x : BitVec 64) : (s.setX r x).rd = s.rd := rfl
@[simp] theorem setX_wr (s : State) (r : XReg) (x : BitVec 64) : (s.setX r x).wr = s.wr := rfl
@[simp] theorem setX_labels (s : State) (r : XReg) (x : BitVec 64) :
    (s.setX r x).labels = s.labels := rfl
@[simp] theorem setX_getV (s : State) (r : XReg) (x : BitVec 64) (r' : VReg) :
    (s.setX r x).getV r' = s.getV r' := rfl

end State

end CC.Arm
