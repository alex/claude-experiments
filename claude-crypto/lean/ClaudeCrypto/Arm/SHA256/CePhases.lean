import ClaudeCrypto.Arm.SHA256.Ce
import ClaudeCrypto.Arm.Sym
import ClaudeCrypto.Arm.StateLemmas

/-!
# Straight-line phases of the AArch64 SHA-256 block function

Each lemma gives the *exact* state after running a phase, as a chain of
register/memory updates of the initial state, for arbitrary register
contents.  All reasoning about what the values mean is done elsewhere
(`CeLemmas.lean`, `CeBlock.lean`).
-/

namespace CC.Arm.SHA256Ce

set_option maxHeartbeats 4000000

/-! ## Four rounds -/

/-- The state after `groupCodeP p off sched`. -/
def groupPost (p off : Nat) (sched : Bool) (s : State) : State :=
  let Wk := vadd32 (s.mem.readW (s.getX .x3 + BitVec.ofNat 64 off) 128) (s.getV (wreg p))
  let nw := if sched then
      sha256su1 (sha256su0 (s.getV (wreg p)) (s.getV (wreg (p + 1)))) (s.getV (wreg (p + 2)))
        (s.getV (wreg (p + 3)))
    else s.getV (wreg p)
  ((((s.setV .v16 Wk).setV (wreg p) nw).setV .v2 (s.getV .v0)).setV .v0
    (sha256hash (s.getV .v0) (s.getV .v1) Wk true)).setV .v1 (sha256hash (s.getV .v0) (s.getV .v1) Wk false)

theorem group_exec (p : Nat) (hp : p < 4) (off : Nat) (sched : Bool) (s : State)
    (hperm : InRegions (s.rd ++ s.wr) (s.getX .x3 + BitVec.ofNat 64 off) 16) :
    ∃ t, execBlock isa (groupCodeP p off sched) s = some (groupPost p off sched s, t) := by
  simp only [State.getX, XRegs.get] at hperm
  interval_cases p <;> cases sched <;>
  · simp only [groupCodeP, groupPost, wreg, Nat.reduceAdd, Nat.reduceMod, List.append_nil,
      List.cons_append, List.nil_append, ite_true, ite_false, Bool.false_eq_true]
    arm_sym [hperm]
    exact ⟨_, rfl⟩

/-! ## Loading the message block -/

/-- The state after `loadMsg`. -/
def loadMsgPost (s : State) : State :=
  let a := s.getX .x1
  ((((((s.setV .v4 (rev32 (s.mem.readW a 128))).setV .v5 (rev32 (s.mem.readW (a + 16#64) 128))).setV
    .v6 (rev32 (s.mem.readW (a + 32#64) 128))).setV .v7 (rev32 (s.mem.readW (a + 48#64) 128))).setX
    .x1 (a + 64#64)).setV .v18 (s.getV .v0)).setV .v19 (s.getV .v1)

theorem loadMsg_exec (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.getX .x1) 16)
    (h1 : InRegions (s.rd ++ s.wr) (s.getX .x1 + 16#64) 16)
    (h2 : InRegions (s.rd ++ s.wr) (s.getX .x1 + 32#64) 16)
    (h3 : InRegions (s.rd ++ s.wr) (s.getX .x1 + 48#64) 16) :
    ∃ t, execBlock isa loadMsg s = some (loadMsgPost s, t) := by
  simp only [State.getX, XRegs.get] at h0 h1 h2 h3
  simp only [loadMsg, loadMsgPost]
  arm_sym [h0, h1, h2, h3]
  exact ⟨_, rfl⟩

/-! ## Adding the saved hash value, counting down -/

def finishPost (s : State) : State :=
  ((s.setV .v0 (vadd32 (s.getV .v0) (s.getV .v18))).setV .v1 (vadd32 (s.getV .v1) (s.getV .v19))).setX
    .x2 (s.getX .x2 - 1#64)

theorem finish_exec (s : State) : ∃ t, execBlock isa finish s = some (finishPost s, t) := by
  simp only [finish, finishPost]
  arm_sym
  exact ⟨_, rfl⟩

/-! ## Loading and storing the hash value -/

def loadStatePost (s : State) : State :=
  ((s.setV .v0 (s.mem.readW (s.getX .x0) 128)).setV .v1 (s.mem.readW (s.getX .x0 + 16#64) 128)).setX
    .x3 (s.labels kLabel)

theorem loadState_exec (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.getX .x0) 16)
    (h1 : InRegions (s.rd ++ s.wr) (s.getX .x0 + 16#64) 16) :
    ∃ t, execBlock isa loadState s = some (loadStatePost s, t) := by
  simp only [State.getX, XRegs.get] at h0 h1
  simp only [loadState, loadStatePost]
  arm_sym [h0, h1]
  exact ⟨_, rfl⟩

def storeStatePost (s : State) : State :=
  { s with mem := (s.mem.writeW (s.getX .x0) (s.getV .v0)).writeW (s.getX .x0 + 16#64) (s.getV .v1) }

theorem storeState_exec (s : State)
    (h0 : InRegions s.wr (s.getX .x0) 16)
    (h1 : InRegions s.wr (s.getX .x0 + 16#64) 16) :
    ∃ t, execBlock isa storeState s = some (storeStatePost s, t) := by
  simp only [State.getX, XRegs.get] at h0 h1
  simp only [storeState, storeStatePost]
  arm_sym [h0, h1]
  exact ⟨_, rfl⟩

end CC.Arm.SHA256Ce
