import ClaudeCrypto.P384.Frame
import ClaudeCrypto.P384.PrimLemmas

/-!
# The statement of the IR-level theorem for the whole verification routine
-/

namespace CC.P384

open CC.Limb CC.Spec.P384

/-- ECDSA-P384 verification of the byte strings in memory: public key `x ‖ y` at `pk`,
digest at `dg`, signature `r ‖ s` at `sg`. -/
def verifyMem (m : Mem) (pk dg sg : Addr) : Bool :=
  verify (inBytes m pk 48) (inBytes m (pk + 48#64) 48) (inBytes m dg 48) (inBytes m sg 48)
    (inBytes m (sg + 48#64) 48)

/-- The preconditions of `main`: the frame (at `r14`) is writable, the constants table (at its
label) holds `constTable`, and the inputs (at `r5`, `r4`, `r0`) are readable and disjoint from
the frame. -/
structure MainPre (s : State) : Prop where
  fr : Within s.wr (s.r 14) frameSize
  cs : Within s.rd (s.labels constLabel) constSize
  tab : ∀ j < constSize, s.mem (s.labels constLabel + BitVec.ofNat 64 j) = constTable[j]!
  sepC : Mem.Sep (s.r 14) frameSize (s.labels constLabel) constSize
  inPk : Within (s.rd ++ s.wr) (s.r 5) 96
  inDg : Within (s.rd ++ s.wr) (s.r 4) 48
  inSg : Within (s.rd ++ s.wr) (s.r 0) 96
  sepPk : Mem.Sep (s.r 14) frameSize (s.r 5) 96
  sepDg : Mem.Sep (s.r 14) frameSize (s.r 4) 48
  sepSg : Mem.Sep (s.r 14) frameSize (s.r 0) 96

/-- The postcondition: register 1 holds the verification result, and only the frame changed. -/
def MainPost (s q : State) : Prop :=
  q.r 1 = BitVec.ofNat 64 (if verifyMem s.mem (s.r 5) (s.r 4) (s.r 0) then 1 else 0) ∧
    q.r 14 = s.r 14 ∧ q.rd = s.rd ∧ q.wr = s.wr ∧ q.labels = s.labels ∧
    Mem.Agree s.mem q.mem ⟨s.r 14, frameSize⟩

end CC.P384
