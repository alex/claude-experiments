import ClaudeCrypto.P384.Point
import ClaudeCrypto.Limb.Test
import ClaudeCrypto.Spec.P384

/-!
# ECDSA-P384 verification in the limb IR

The whole verification routine, written once in the limb IR:

* inputs are read big-endian from the pointers in registers 5 (public key
  `x ‖ y`), 4 (digest) and 0 (signature `r ‖ s`); register 14 points to a
  frame of `frameSize` bytes and register 13 is set to the constants table;
* the result (`1` valid, `0` invalid) is left in register 1.

Field elements live in 48-byte frame slots (`FOp.off 0 i = 48·i`), in
Montgomery form, and are manipulated by the field programs of
`Limb/FProg.lean` (modulo `p` for the point arithmetic, modulo `n` for the
scalars).
-/

namespace CC.P384

open CC.Limb CC.Spec.P384

/-! ## Constants -/

/-- `-N⁻¹ mod 2^64` (for odd `N`), by Newton iteration. -/
def negInv64 (N : Nat) : Nat :=
  let step (x : Nat) : Nat := x * (2 ^ 65 + 2 - N * x % 2 ^ 64) % 2 ^ 64
  let inv := step (step (step (step (step (step 1)))))
  (2 ^ 64 - inv) % 2 ^ 64

def R : Nat := 2 ^ 384

/-- Byte offsets in the constants table. -/
def cP : Nat := 0
def cMpP : Nat := 48
def cN : Nat := 56
def cMpN : Nat := 104
def cR2P : Nat := 112
def cOneP : Nat := 160
def cGx : Nat := 208
def cGy : Nat := 256
def cB : Nat := 304
def cR2N : Nat := 352
def cOneN : Nat := 400
def cNm2 : Nat := 448
def cNm : Nat := 496
def cPmn : Nat := 544

/-- The constants, in table order (each is `(value, bytes)`). -/
def constList : List (Nat × Nat) :=
  [ (p, 48), (negInv64 p, 8), (n, 48), (negInv64 n, 8),
    (R * R % p, 48), (R % p, 48), (Gx * R % p, 48), (Gy * R % p, 48), (b * R % p, 48),
    (R * R % n, 48), (R % n, 48), (n - 2, 48), (n * R % p, 48), (p - n, 48) ]

def leBytes (x k : Nat) : List (BitVec 8) := (List.range k).map fun i => BitVec.ofNat 8 (x / 256 ^ i)

def constTable : List (BitVec 8) := (constList.map fun c => leBytes c.1 c.2).flatten

def constLabel : String := ".Lcc_p384_consts"

/-! ## Frame slots -/

/-- Accumulator `(X, Y, Z)`: slots 0–2; operand: 3–5; temporaries: 6–14. -/
def sG : Nat := 15
def sQ : Nat := 18
def sGQ : Nat := 21
def sU1 : Nat := 24
def sU2 : Nat := 25
def sR : Nat := 26
def sS : Nat := 27
def sE : Nat := 28
def sR2P : Nat := 29
def sB : Nat := 30
def sR2N : Nat := 31
def sOneN : Nat := 32
def sExp : Nat := 33
def sNm : Nat := 34
def sQx : Nat := 35
def sQy : Nat := 36
def nSlots : Nat := 37
/-- The loop counter. -/
def cntOff : Nat := 48 * nSlots
def frameSize : Nat := 48 * nSlots + 8

/-! ## Primitives -/

abbrev LCode := Code Instr Cond

def slotOff (i : Nat) : Nat := FOp.off 0 i

/-- Frame slot `d := ` frame slot `a`. -/
def copySlot (d a : Nat) : List Instr :=
  (List.range 6).flatMap fun k => [.ld 9 14 (slotOff a + 8 * k), .st 14 (slotOff d + 8 * k) 9]

/-- Frame slot `d := ` the constant at byte `c` of the table. -/
def copyConst (d c : Nat) : List Instr :=
  (List.range 6).flatMap fun k => [.ld 9 13 (c + 8 * k), .st 14 (slotOff d + 8 * k) 9]

def zeroSlot (d : Nat) : List Instr :=
  .movi 9 0 :: (List.range 6).map fun k => .st 14 (slotOff d + 8 * k) 9

/-- Frame slot `d := ` the 48 big-endian bytes at `b + off`. -/
def loadBE (d : Nat) (b : Var) (off : Nat) : List Instr :=
  (List.range 6).flatMap fun k => [.ldbe 9 b (off + 40 - 8 * k), .st 14 (slotOff d + 8 * k) 9]

/-- `t := ` all ones if slot `a` `<` the constant at `c`, else `0`. -/
def ltConst (a c : Nat) (t : Var) : List Instr :=
  [.ld 9 14 (slotOff a), .ld 8 13 c, .sub 9 8] ++
  ((List.range 5).flatMap fun k =>
    [.ld 9 14 (slotOff a + 8 * (k + 1)), .ld 8 13 (c + 8 * (k + 1)), .sbb 9 8]) ++
  [.mask t, .clrc]

/-- `d := ` the top bit of slot `a`; then shift slot `a` left by one bit. -/
def topBit (a : Nat) (d : Var) : List Instr :=
  [.ld d 14 (slotOff a + 40), .shr d 63] ++
  ((List.range 5).flatMap fun j =>
    let k := 5 - j
    [.ld 7 14 (slotOff a + 8 * k), .shl 7 1, .ld 8 14 (slotOff a + 8 * (k - 1)), .shr 8 63, .or 7 8,
     .st 14 (slotOff a + 8 * k) 7]) ++
  [.ld 7 14 (slotOff a), .shl 7 1, .st 14 (slotOff a) 7]

def cntInit (k : Nat) : List Instr := [.movi 9 (BitVec.ofNat 64 k), .st 14 cntOff 9]
def cntDec : List Instr := [.ld 9 14 cntOff, .subi 9 1, .st 14 cntOff 9]

/-- `if slot a = 0 then t else e`. -/
def ifZero (a : Nat) (t e : LCode) : LCode := .seq (.block (orSlot 10 (slotOff a))) (.ite (.eqz 10) t e)

def pcode (ops : List FOp) : LCode := FProg.code cP cMpP 0 ops
def ncode (ops : List FOp) : LCode := FProg.code cN cMpN 0 ops

def ret (v : Nat) : LCode := .block [.movi 1 (BitVec.ofNat 64 v)]

/-! ## Point addition with all special cases -/

def copy3 (d a : Nat) : List Instr := copySlot d a ++ copySlot (d + 1) (a + 1) ++ copySlot (d + 2) (a + 2)

/-- Accumulator (slots 0–2) `+=` operand (slots 3–5). -/
def addCode : LCode :=
  ifZero 2 (.block (copy3 0 3))
    (ifZero 5 (.block [])
      (.seq (pcode (addPre 0 1 2 3 4 5 6))
        (ifZero 10
          (ifZero 11 (pcode (dblProg 0 1 2 6)) (.block (zeroSlot 2)))
          (pcode (addPost 0 1 2 5 6)))))

/-! ## The scalar part: `u₁ = e·s⁻¹`, `u₂ = r·s⁻¹ (mod n)` -/

/-- Slot 7 `:= ` slot 6 `^ (n − 2)` by square-and-multiply over the bits of slot `sExp`. -/
def invLoop : LCode :=
  .loop (.seq (ncode [.mul 7 7 7]) (.seq (.block (topBit sExp 10))
    (.seq (.ite (.nez 10) (ncode [.mul 7 7 6]) (.block [])) (.block cntDec)))) (.nez 9)

def scalars : LCode :=
  .seq (ncode [.mul 6 sS sR2N]) (.seq (.block (copySlot 7 sOneN ++ cntInit 384))
    (.seq invLoop (ncode [.mul sU1 7 sE, .mul sU2 7 sR])))

/-! ## The double-scalar multiplication `u₁·G + u₂·Q` -/

def ladder : LCode :=
  .loop (.seq (pcode (dblProg 0 1 2 6))
    (.seq (.block (topBit sU1 10 ++ topBit sU2 11 ++ [.mov 12 10, .or 12 11]))
    (.seq (.ite (.nez 10) (.ite (.nez 11) (.block (copy3 3 sGQ)) (.block (copy3 3 sG)))
                          (.ite (.nez 11) (.block (copy3 3 sQ)) (.block [])))
    (.seq (.ite (.nez 12) addCode (.block [])) (.block cntDec))))) (.nez 9)

def pointPart : LCode :=
  .seq (.block (copy3 0 sG ++ copy3 3 sQ)) (.seq addCode
    (.seq (.block (copy3 sGQ 0 ++ zeroSlot 0 ++ zeroSlot 1 ++ zeroSlot 2 ++ cntInit 384)) ladder))

/-! ## The final comparison `x_R ≡ r (mod n)` -/

def final : LCode :=
  ifZero 2 (ret 0)
    (.seq (pcode [.mul 6 sR sR2P, .mul 7 2 2, .mul 8 6 7, .sub 9 0 8])
      (ifZero 9 (ret 1)
        (.seq (.block (ltConst sR cPmn 10))
          (.ite (.nez 10)
            (.seq (pcode [.mul 6 sNm 7, .add 8 8 6, .sub 9 0 8]) (ifZero 9 (ret 1) (ret 0)))
            (ret 0)))))

/-! ## Input decoding and validation -/

def setup : List Instr :=
  [.lea 13 constLabel 0] ++
  loadBE sQx 5 0 ++ loadBE sQy 5 48 ++ loadBE sE 4 0 ++ loadBE sR 0 0 ++ loadBE sS 0 48 ++
  copyConst sG cGx ++ copyConst (sG + 1) cGy ++ copyConst (sG + 2) cOneP ++ copyConst (sQ + 2) cOneP ++
  copyConst sR2P cR2P ++ copyConst sB cB ++ copyConst sR2N cR2N ++ copyConst sOneN cOneN ++
  copyConst sExp cNm2 ++ copyConst sNm cNm

/-- `y² − (x³ − 3x + b)` into slot 9, with `(x, y)` into slots `sQ, sQ + 1` (Montgomery form). -/
def onCurveProg : List FOp :=
  [ .mul sQ sQx sR2P, .mul (sQ + 1) sQy sR2P,
    .mul 6 (sQ + 1) (sQ + 1), .mul 7 sQ sQ, .mul 7 7 sQ, .add 8 sQ sQ, .add 8 8 sQ, .sub 7 7 8,
    .add 7 7 sB, .sub 9 6 7 ]

def check (pre : List Instr) (ok : LCode) : LCode := .seq (.block pre) (.ite (.nez 10) ok (ret 0))

def main : LCode :=
  .seq (.block setup)
    (check (ltConst sQx cP 10) <| check (ltConst sQy cP 10) <|
     check (ltConst sR cN 10) <| ifZero sR (ret 0) <|
     check (ltConst sS cN 10) <| ifZero sS (ret 0) <|
     .seq (pcode onCurveProg) <| ifZero 9 (.seq scalars (.seq pointPart final)) (ret 0))

end CC.P384
