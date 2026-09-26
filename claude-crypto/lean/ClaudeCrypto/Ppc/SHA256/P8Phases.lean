import ClaudeCrypto.Ppc.SHA256.P8Lemmas
import ClaudeCrypto.Ppc.Sym
import ClaudeCrypto.Ppc.StateLemmas

/-!
# Straight-line phases of the ppc64le SHA-256 block function

Each lemma gives the *exact* state after running a phase, as a chain of
register/memory updates of the initial state, for arbitrary register
contents.  All reasoning about what the values mean is done elsewhere
(`P8Lemmas.lean`, `P8Block.lean`).
-/

namespace CC.Ppc.SHA256P8

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## One round -/

/-- The state after `roundCode r kw` where `kw` holds `x`. -/
def roundPost (r : Nat) (x : BitVec 128) (s : State) : State :=
  let a := s.getV (varReg r 0); let b := s.getV (varReg r 1); let c := s.getV (varReg r 2)
  let d := s.getV (varReg r 3); let e := s.getV (varReg r 4); let f := s.getV (varReg r 5)
  let g := s.getV (varReg r 6); let h := s.getV (varReg r 7)
  (((s.setV .v14 (vsel b c (a ^^^ b))).setV .v15 (vshasigmaw a true 0)).setV (varReg r 3)
    (newE d e f g h x)).setV (varReg r 7) (newA a b c e f g h x)

/-- The `K + W` word used by round `r` (mod 8) of a group. -/
def kwOf (r : Nat) (s : State) : BitVec 128 :=
  if r % 4 = 0 then s.getV .v12 else vsldoi (s.getV .v12) (s.getV .v12) (4 * (r % 4))

/-- The state after `stepCode r`. -/
def stepPost (r : Nat) (s : State) : State :=
  if r % 4 = 0 then roundPost r (kwOf r s) s else roundPost r (kwOf r s) (s.setV .v13 (kwOf r s))

theorem step_exec (r : Nat) (hr : r < 8) (s : State) :
    ∃ t, execBlock isa (stepCode r) s = some (stepPost r s, t) := by
  interval_cases r <;>
  · simp only [stepCode, roundCode, stepPost, roundPost, kwOf, varReg, newA, newE, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, ite_true, ite_false, reduceIte, List.cons_append,
      List.nil_append]
    ppc_sym
    exact ⟨_, rfl⟩


/-! ## Group head: round constants, `K + W`, message schedule -/

/-- The value loaded by `lxvw4x` from `ea`. -/
def lxv (m : Mem) (ea : Addr) : BitVec 128 :=
  m.readW ea 32 ++ m.readW (ea + 4) 32 ++ m.readW (ea + 8) 32 ++ m.readW (ea + 12) 32

/-- The final value of the temporary `v14` after `schedCode`. -/
def schedTmp (xa xb xc xd z : BitVec 128) : BitVec 128 :=
  let a1 := vadduwm xa (vshasigmaw (vsldoi xa xb 4) false 0)
  let a2 := vadduwm a1 (vsldoi xc xd 4)
  let a3 := vadduwm a2 (vshasigmaw (vsldoi xd z 8) false 15)
  vshasigmaw (vsldoi z a3 8) false 15

/-- The state after `headCode p ra rb sched`. -/
def headPost (p : Nat) (ra rb : GReg) (sched : Bool) (s : State) : State :=
  let kv := lxv s.mem (s.ea ra rb)
  let s1 := (s.setV .v14 kv).setV .v12 (vadduwm (s.getV (wreg p)) kv)
  if sched then
    (s1.setV .v14 (schedTmp (s.getV (wreg p)) (s.getV (wreg (p + 1))) (s.getV (wreg (p + 2)))
      (s.getV (wreg (p + 3))) (s.getV .v18))).setV (wreg p)
      (schedVal (s.getV (wreg p)) (s.getV (wreg (p + 1))) (s.getV (wreg (p + 2)))
        (s.getV (wreg (p + 3))) (s.getV .v18))
  else s1

theorem head_exec (p : Nat) (hp : p < 4) (ra rb : GReg) (sched : Bool) (s : State)
    (hperm : InRegions (s.rd ++ s.wr) (s.ea ra rb) 16) :
    ∃ t, execBlock isa (headCode p ra rb sched) s = some (headPost p ra rb sched s, t) := by
  interval_cases p <;> cases sched <;>
  · simp only [headCode, schedCode, headPost, schedVal, schedTmp, wreg, lxv, Nat.reduceAdd,
      Nat.reduceMod, List.append_nil, List.cons_append, List.nil_append, ite_true, ite_false,
      Bool.false_eq_true]
    simp only [CC.execBlock, CC.Ppc.isa, CC.Ppc.exec, CC.Ppc.addrs, hperm, ite_true,
      Option.map_some]
    ppc_sym
    exact ⟨_, rfl⟩

/-! ## Unpacking the hash value into the working variables -/

def unpackPost (s : State) : State :=
  let x := s.getV .v16; let y := s.getV .v17
  (((((((s.setV .v0 (x ||| x)).setV .v1 (vsldoi x x 4)).setV .v2 (vsldoi x x 8)).setV .v3
    (vsldoi x x 12)).setV .v4 (y ||| y)).setV .v5 (vsldoi y y 4)).setV .v6 (vsldoi y y 8)).setV .v7
    (vsldoi y y 12)

theorem unpack_exec (s : State) : ∃ t, execBlock isa unpack s = some (unpackPost s, t) := by
  simp only [unpack, unpackPost]
  ppc_sym
  exact ⟨_, rfl⟩

/-! ## Loading the message block -/

def loadMsgPost (s : State) : State :=
  let a := s.getG .r4
  let m := s.getV .v19
  let l0 := lxv s.mem a; let l1 := lxv s.mem (a + s.getG .r7)
  let l2 := lxv s.mem (a + s.getG .r8); let l3 := lxv s.mem (a + s.getG .r9)
  (((((s.setV .v8 (vperm l0 l0 m)).setV .v9 (vperm l1 l1 m)).setV .v10 (vperm l2 l2 m)).setV .v11
    (vperm l3 l3 m)).setG .r4 (a + 64#64))

theorem loadMsg_exec (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.getG .r4) 16)
    (h1 : InRegions (s.rd ++ s.wr) (s.getG .r4 + s.getG .r7) 16)
    (h2 : InRegions (s.rd ++ s.wr) (s.getG .r4 + s.getG .r8) 16)
    (h3 : InRegions (s.rd ++ s.wr) (s.getG .r4 + s.getG .r9) 16) :
    ∃ t, execBlock isa loadMsg s = some (loadMsgPost s, t) := by
  simp only [State.getG, GRegs.get] at h0 h1 h2 h3
  simp only [loadMsg, loadMsgPost, lxv]
  ppc_sym [h0, h1, h2, h3]
  exact ⟨_, rfl⟩

/-! ## Adding the working variables into the hash value, counting down -/

def finishPost (s : State) : State :=
  let p1 := xxpermdi (vmrghw (s.getV .v0) (s.getV .v1)) (vmrghw (s.getV .v2) (s.getV .v3)) 0
  let p2 := xxpermdi (vmrghw (s.getV .v4) (s.getV .v5)) (vmrghw (s.getV .v6) (s.getV .v7)) 0
  let n := s.getG .r5 + 1#64
  { (((((s.setV .v13 p1).setV .v15 (vmrghw (s.getV .v6) (s.getV .v7))).setV .v14 p2).setV .v16
      (vadduwm (s.getV .v16) p1)).setV .v17 (vadduwm (s.getV .v17) p2)).setG .r5 n with
    lt := some (BitVec.ult n 0#64), gt := some (BitVec.ult 0#64 n), eq := some (n == 0#64) }

theorem finish_exec (s : State) : ∃ t, execBlock isa finish s = some (finishPost s, t) := by
  simp only [finish, finishPost]
  ppc_sym
  exact ⟨_, rfl⟩

/-! ## Setup: the table address, constants, the hash value -/

def setupPost (s : State) : State :=
  let k := s.labels kLabel
  let st := s.getG .r3
  (((((((((((((s.setG .r5 (~~~(s.getG .r5) + 1#64)).setG .r0 s.lr).setG .r6 k).setG .r10 (k + 64#64)).setG .r11 (k + 128#64)).setG .r12
    (k + 192#64)).setG .r0 (k + 256#64)).setG .r7 16#64).setG .r8 32#64).setG .r9 48#64).setV .v19
    (lxv s.mem (k + 256#64))).setV .v18 (s.getV .v18 ^^^ s.getV .v18)).setV .v16 (lxv s.mem st)).setV
    .v17 (lxv s.mem (st + 16#64))

theorem setup_exec (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.labels kLabel + 256#64) 16)
    (h1 : InRegions (s.rd ++ s.wr) (s.getG .r3) 16)
    (h2 : InRegions (s.rd ++ s.wr) (s.getG .r3 + 16#64) 16) :
    ∃ t, execBlock isa setup s = some (setupPost s, t) := by
  simp only [State.getG, GRegs.get] at h1 h2
  simp only [setup, setupPost, lxv]
  ppc_sym [h0, h1, h2]
  exact ⟨_, rfl⟩

/-! ## Storing the hash value, the initial comparison -/

def storePost (s : State) : State :=
  let st := s.getG .r3
  let x := s.getV .v16; let y := s.getV .v17
  let st2 := st + s.getG .r7
  { s with mem := (((((((s.mem.writeW st (word x 0)).writeW (st + 4) (word x 1)).writeW (st + 8)
      (word x 2)).writeW (st + 12) (word x 3)).writeW st2 (word y 0)).writeW (st2 + 4) (word y 1)).writeW
      (st2 + 8) (word y 2)).writeW (st2 + 12) (word y 3) }

theorem store_exec (s : State)
    (h0 : InRegions s.wr (s.getG .r3) 16)
    (h1 : InRegions s.wr (s.getG .r3 + s.getG .r7) 16) :
    ∃ t, execBlock isa storeState s = some (storePost s, t) := by
  simp only [State.getG, GRegs.get] at h0 h1
  simp only [storeState, storePost]
  ppc_sym [h0, h1]
  exact ⟨_, rfl⟩

def cmpPost (s : State) : State :=
  { s with lt := some (BitVec.ult (s.getG .r5) 0#64), gt := some (BitVec.ult 0#64 (s.getG .r5)),
           eq := some (s.getG .r5 == 0#64) }

theorem cmp_exec (s : State) : ∃ t, execBlock isa [.cmpldi .r5 0] s = some (cmpPost s, t) := by
  simp only [cmpPost]
  ppc_sym
  exact ⟨_, rfl⟩

end CC.Ppc.SHA256P8
