import ClaudeCrypto.Framework.Code

/-!
# AArch64 machine model

A model of the subset of AArch64 (ARMv8-A, little-endian, EL0 user code)
used by our implementations.  This file is part of the trusted computing
base: each instruction's semantics here must agree with the *Arm
Architecture Reference Manual for A-profile* (Arm ARM, DDI 0487).  The
pseudocode functions of the Arm ARM that we transcribe are named in the
comments.  (The semantics of the vector/crypto instructions and of `subs` are
additionally cross-checked against QEMU by `test/arm_insn_test.c` +
`test/ArmInsnCheck.lean`, and the complete generated function by the
differential tests in `test/`; see `test/run_aarch64.sh`.)

Modelling choices:
* State: `X0`–`X30`, `SP`, `V0`–`V31` (128 bits), the NZCV flags, memory,
  and the permitted memory regions.  `labels` gives the (link-time) address
  of each data label in the program text; `adr` reads it.
* Each flag is an `Option Bool`; `none` means "unknown/undefined".  Reading an
  undefined flag faults, so verified code never depends on one.
* Register number 31 (`XZR`/`SP`) is not available as an operand of the
  modelled instructions: all operands are `X0`–`X30`.
* Memory accesses must lie within the state's permitted regions: loads
  within `rd ++ wr`, stores within `wr`; otherwise the instruction faults.
  (Each 16-byte register transfer of a multi-register `ld1`/`st1` is checked
  separately, like the per-element accesses of the Arm ARM pseudocode.)
  Alignment is not modelled: all modelled accesses are to Normal memory, for
  which unaligned SIMD&FP accesses are permitted when SCTLR_EL1.A = 0, as in
  Linux user space.
* Little-endian only (`SCTLR_EL1.E0E = 0`): multi-byte loads and stores
  are little-endian, which also makes the element size of `ld1`/`st1`
  irrelevant to their effect (it only matters for big-endian data).
* Immediate operands are unrestricted naturals in the model; the assembler
  rejects any that are not encodable, so the emitted code is exactly the
  modelled code.
-/

namespace CC.Arm

inductive XReg
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7
  | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
  | x24 | x25 | x26 | x27 | x28 | x29 | x30
  deriving DecidableEq, Repr, Inhabited

structure XRegs where
  x0 : BitVec 64
  x1 : BitVec 64
  x2 : BitVec 64
  x3 : BitVec 64
  x4 : BitVec 64
  x5 : BitVec 64
  x6 : BitVec 64
  x7 : BitVec 64
  x8 : BitVec 64
  x9 : BitVec 64
  x10 : BitVec 64
  x11 : BitVec 64
  x12 : BitVec 64
  x13 : BitVec 64
  x14 : BitVec 64
  x15 : BitVec 64
  x16 : BitVec 64
  x17 : BitVec 64
  x18 : BitVec 64
  x19 : BitVec 64
  x20 : BitVec 64
  x21 : BitVec 64
  x22 : BitVec 64
  x23 : BitVec 64
  x24 : BitVec 64
  x25 : BitVec 64
  x26 : BitVec 64
  x27 : BitVec 64
  x28 : BitVec 64
  x29 : BitVec 64
  x30 : BitVec 64
  deriving DecidableEq

namespace XRegs
def get (g : XRegs) : XReg → BitVec 64
  | .x0 => g.x0 | .x1 => g.x1 | .x2 => g.x2 | .x3 => g.x3
  | .x4 => g.x4 | .x5 => g.x5 | .x6 => g.x6 | .x7 => g.x7
  | .x8 => g.x8 | .x9 => g.x9 | .x10 => g.x10 | .x11 => g.x11
  | .x12 => g.x12 | .x13 => g.x13 | .x14 => g.x14 | .x15 => g.x15
  | .x16 => g.x16 | .x17 => g.x17 | .x18 => g.x18 | .x19 => g.x19
  | .x20 => g.x20 | .x21 => g.x21 | .x22 => g.x22 | .x23 => g.x23
  | .x24 => g.x24 | .x25 => g.x25 | .x26 => g.x26 | .x27 => g.x27
  | .x28 => g.x28 | .x29 => g.x29 | .x30 => g.x30

def set (g : XRegs) (r : XReg) (v : BitVec 64) : XRegs :=
  match r with
  | .x0 => { g with x0 := v } | .x1 => { g with x1 := v }
  | .x2 => { g with x2 := v } | .x3 => { g with x3 := v }
  | .x4 => { g with x4 := v } | .x5 => { g with x5 := v }
  | .x6 => { g with x6 := v } | .x7 => { g with x7 := v }
  | .x8 => { g with x8 := v } | .x9 => { g with x9 := v }
  | .x10 => { g with x10 := v } | .x11 => { g with x11 := v }
  | .x12 => { g with x12 := v } | .x13 => { g with x13 := v }
  | .x14 => { g with x14 := v } | .x15 => { g with x15 := v }
  | .x16 => { g with x16 := v } | .x17 => { g with x17 := v }
  | .x18 => { g with x18 := v } | .x19 => { g with x19 := v }
  | .x20 => { g with x20 := v } | .x21 => { g with x21 := v }
  | .x22 => { g with x22 := v } | .x23 => { g with x23 := v }
  | .x24 => { g with x24 := v } | .x25 => { g with x25 := v }
  | .x26 => { g with x26 := v } | .x27 => { g with x27 := v }
  | .x28 => { g with x28 := v } | .x29 => { g with x29 := v }
  | .x30 => { g with x30 := v }
end XRegs

inductive VReg
  | v0 | v1 | v2 | v3 | v4 | v5 | v6 | v7
  | v8 | v9 | v10 | v11 | v12 | v13 | v14 | v15
  | v16 | v17 | v18 | v19 | v20 | v21 | v22 | v23
  | v24 | v25 | v26 | v27 | v28 | v29 | v30 | v31
  deriving DecidableEq, Repr, Inhabited

structure VRegs where
  v0 : BitVec 128
  v1 : BitVec 128
  v2 : BitVec 128
  v3 : BitVec 128
  v4 : BitVec 128
  v5 : BitVec 128
  v6 : BitVec 128
  v7 : BitVec 128
  v8 : BitVec 128
  v9 : BitVec 128
  v10 : BitVec 128
  v11 : BitVec 128
  v12 : BitVec 128
  v13 : BitVec 128
  v14 : BitVec 128
  v15 : BitVec 128
  v16 : BitVec 128
  v17 : BitVec 128
  v18 : BitVec 128
  v19 : BitVec 128
  v20 : BitVec 128
  v21 : BitVec 128
  v22 : BitVec 128
  v23 : BitVec 128
  v24 : BitVec 128
  v25 : BitVec 128
  v26 : BitVec 128
  v27 : BitVec 128
  v28 : BitVec 128
  v29 : BitVec 128
  v30 : BitVec 128
  v31 : BitVec 128
  deriving DecidableEq

namespace VRegs
def get (g : VRegs) : VReg → BitVec 128
  | .v0 => g.v0 | .v1 => g.v1 | .v2 => g.v2 | .v3 => g.v3
  | .v4 => g.v4 | .v5 => g.v5 | .v6 => g.v6 | .v7 => g.v7
  | .v8 => g.v8 | .v9 => g.v9 | .v10 => g.v10 | .v11 => g.v11
  | .v12 => g.v12 | .v13 => g.v13 | .v14 => g.v14 | .v15 => g.v15
  | .v16 => g.v16 | .v17 => g.v17 | .v18 => g.v18 | .v19 => g.v19
  | .v20 => g.v20 | .v21 => g.v21 | .v22 => g.v22 | .v23 => g.v23
  | .v24 => g.v24 | .v25 => g.v25 | .v26 => g.v26 | .v27 => g.v27
  | .v28 => g.v28 | .v29 => g.v29 | .v30 => g.v30 | .v31 => g.v31

def set (g : VRegs) (r : VReg) (v : BitVec 128) : VRegs :=
  match r with
  | .v0 => { g with v0 := v } | .v1 => { g with v1 := v }
  | .v2 => { g with v2 := v } | .v3 => { g with v3 := v }
  | .v4 => { g with v4 := v } | .v5 => { g with v5 := v }
  | .v6 => { g with v6 := v } | .v7 => { g with v7 := v }
  | .v8 => { g with v8 := v } | .v9 => { g with v9 := v }
  | .v10 => { g with v10 := v } | .v11 => { g with v11 := v }
  | .v12 => { g with v12 := v } | .v13 => { g with v13 := v }
  | .v14 => { g with v14 := v } | .v15 => { g with v15 := v }
  | .v16 => { g with v16 := v } | .v17 => { g with v17 := v }
  | .v18 => { g with v18 := v } | .v19 => { g with v19 := v }
  | .v20 => { g with v20 := v } | .v21 => { g with v21 := v }
  | .v22 => { g with v22 := v } | .v23 => { g with v23 := v }
  | .v24 => { g with v24 := v } | .v25 => { g with v25 := v }
  | .v26 => { g with v26 := v } | .v27 => { g with v27 := v }
  | .v28 => { g with v28 := v } | .v29 => { g with v29 := v }
  | .v30 => { g with v30 := v } | .v31 => { g with v31 := v }
end VRegs

/-! ## 32-bit lanes of vector registers -/

/-- `Elem[x, e, 32]`: the `e`-th 32-bit element of a 128-bit vector (element 0 is
bits 31:0). -/
def elem (x : BitVec 128) (e : Nat) : BitVec 32 := x.extractLsb' (32 * e) 32

/-- The 128-bit vector with 32-bit elements `e0, e1, e2, e3` (element 0 least
significant). -/
def vec4 (e0 e1 e2 e3 : BitVec 32) : BitVec 128 := e3 ++ e2 ++ e1 ++ e0

/-- `ADD Vd.4S, Vn.4S, Vm.4S`: `Elem[result, e, 32] = Elem[op1, e, 32] + Elem[op2, e, 32]`. -/
def vadd32 (a b : BitVec 128) : BitVec 128 :=
  vec4 (elem a 0 + elem b 0) (elem a 1 + elem b 1) (elem a 2 + elem b 2) (elem a 3 + elem b 3)

/-- Reverse the four bytes of a 32-bit container: byte 0 (bits 7:0) becomes byte 3. -/
def rev8in32 (x : BitVec 32) : BitVec 32 :=
  x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8

/-- `REV32 Vd.16B, Vn.16B`: reverse the order of the 8-bit elements within each
32-bit container (the Arm ARM `REV16/REV32/REV64` pseudocode with
`esize = 8`, `container_size = 32`). -/
def rev32 (x : BitVec 128) : BitVec 128 :=
  vec4 (rev8in32 (elem x 0)) (rev8in32 (elem x 1)) (rev8in32 (elem x 2)) (rev8in32 (elem x 3))

/-! ## The SHA-256 instructions (FEAT_SHA256)

Transcriptions of the Arm ARM shared pseudocode functions `SHAchoose`,
`SHAmajority`, `SHAhashSIGMA0`, `SHAhashSIGMA1` and `SHA256hash`, and of the
`SHA256SU0` / `SHA256SU1` instruction pseudocode. -/

/-- `SHAchoose(x, y, z) = ((y EOR z) AND x) EOR z` -/
def SHAchoose (x y z : BitVec 32) : BitVec 32 := ((y ^^^ z) &&& x) ^^^ z
/-- `SHAmajority(x, y, z) = ((x AND y) OR ((x OR y) AND z))` -/
def SHAmajority (x y z : BitVec 32) : BitVec 32 := (x &&& y) ||| ((x ||| y) &&& z)
/-- `SHAhashSIGMA0(x) = ROR(x, 2) EOR ROR(x, 13) EOR ROR(x, 22)` -/
def SHAhashSIGMA0 (x : BitVec 32) : BitVec 32 := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
/-- `SHAhashSIGMA1(x) = ROR(x, 6) EOR ROR(x, 11) EOR ROR(x, 25)` -/
def SHAhashSIGMA1 (x : BitVec 32) : BitVec 32 := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- One iteration `e` of the loop of `SHA256hash`:
```
chs = SHAchoose(Y<31:0>, Y<63:32>, Y<95:64>);
maj = SHAmajority(X<31:0>, X<63:32>, X<95:64>);
t = Y<127:96> + SHAhashSIGMA1(Y<31:0>) + chs + Elem[W, e, 32];
X<127:96> = t + X<127:96>;
Y<127:96> = t + SHAhashSIGMA0(X<31:0>) + maj;
bits(256) yx = ROL(Y : X, 32);
Y = yx<255:128>;
X = yx<127:0>;
```
The pair is `(X, Y)`. -/
def sha256hashIter (W : BitVec 128) (e : Nat) (XY : BitVec 128 × BitVec 128) :
    BitVec 128 × BitVec 128 :=
  let chs := SHAchoose (XY.2.extractLsb' 0 32) (XY.2.extractLsb' 32 32) (XY.2.extractLsb' 64 32)
  let maj := SHAmajority (XY.1.extractLsb' 0 32) (XY.1.extractLsb' 32 32) (XY.1.extractLsb' 64 32)
  let t := XY.2.extractLsb' 96 32 + SHAhashSIGMA1 (XY.2.extractLsb' 0 32) + chs + elem W e
  let X : BitVec 128 := (t + XY.1.extractLsb' 96 32) ++ XY.1.extractLsb' 0 96
  let Y : BitVec 128 := (t + SHAhashSIGMA0 (X.extractLsb' 0 32) + maj) ++ XY.2.extractLsb' 0 96
  let yx : BitVec 256 := (Y ++ X).rotateLeft 32
  (yx.extractLsb' 0 128, yx.extractLsb' 128 128)

/-- `SHA256hash(X, Y, W, part1)`: `for e = 0 to 3 …; return (if part1 then X else Y)`. -/
def sha256hash (X Y W : BitVec 128) (part1 : Bool) : BitVec 128 :=
  let XY := sha256hashIter W 3 (sha256hashIter W 2 (sha256hashIter W 1 (sha256hashIter W 0 (X, Y))))
  if part1 then XY.1 else XY.2

/-- The `SHA256SU0 Vd.4S, Vn.4S` computation with `operand1 = V[d]`, `operand2 = V[n]`:
```
T = operand2<31:0> : operand1<127:32>;
for e = 0 to 3
    elt = Elem[T, e, 32];
    elt = ROR(elt, 7) EOR ROR(elt, 18) EOR LSR(elt, 3);
    Elem[result, e, 32] = elt + Elem[operand1, e, 32];
```
-/
def sha256su0 (op1 op2 : BitVec 128) : BitVec 128 :=
  let T : BitVec 128 := op2.extractLsb' 0 32 ++ op1.extractLsb' 32 96
  let f (e : Nat) : BitVec 32 :=
    let elt := elem T e
    (elt.rotateRight 7 ^^^ elt.rotateRight 18 ^^^ elt >>> 3) + elem op1 e
  vec4 (f 0) (f 1) (f 2) (f 3)

/-- The `SHA256SU1 Vd.4S, Vn.4S, Vm.4S` computation with `operand1 = V[d]`,
`operand2 = V[n]`, `operand3 = V[m]`:
```
T0 = operand3<31:0> : operand2<127:32>;
T1 = operand3<127:64>;
for e = 0 to 1
    elt = Elem[T1, e, 32];
    elt = ROR(elt, 17) EOR ROR(elt, 19) EOR LSR(elt, 10);
    elt = elt + Elem[operand1, e, 32] + Elem[T0, e, 32];
    Elem[result, e, 32] = elt;
T1 = result<63:0>;
for e = 2 to 3
    elt = Elem[T1, e-2, 32];
    elt = ROR(elt, 17) EOR ROR(elt, 19) EOR LSR(elt, 10);
    elt = elt + Elem[operand1, e, 32] + Elem[T0, e, 32];
    Elem[result, e, 32] = elt;
```
-/
def sha256su1 (op1 op2 op3 : BitVec 128) : BitVec 128 :=
  let T0 : BitVec 128 := op3.extractLsb' 0 32 ++ op2.extractLsb' 32 96
  let T1 : BitVec 64 := op3.extractLsb' 64 64
  let s1 (elt : BitVec 32) : BitVec 32 := elt.rotateRight 17 ^^^ elt.rotateRight 19 ^^^ elt >>> 10
  let r0 := s1 (T1.extractLsb' 0 32) + elem op1 0 + elem T0 0
  let r1 := s1 (T1.extractLsb' 32 32) + elem op1 1 + elem T0 1
  let T1' : BitVec 64 := r1 ++ r0
  let r2 := s1 (T1'.extractLsb' 0 32) + elem op1 2 + elem T0 2
  let r3 := s1 (T1'.extractLsb' 32 32) + elem op1 3 + elem T0 3
  vec4 r0 r1 r2 r3

/-! ## Machine state -/

structure State where
  x : XRegs
  sp : BitVec 64
  v : VRegs
  /-- The N, Z, C and V condition flags. -/
  nf : Option Bool
  zf : Option Bool
  cf : Option Bool
  vf : Option Bool
  mem : Mem
  /-- Regions the code may read (in addition to `wr`). -/
  rd : List Region
  /-- Regions the code may read and write. -/
  wr : List Region
  /-- The address of each data label of the program (fixed at link time). -/
  labels : String → Addr

/-- Arrangement specifier of `ld1`/`st1` (only affects printing: see the module doc). -/
inductive Arr | b16 | s4
  deriving DecidableEq, Repr

inductive Instr
  /-- `LDR Qt, [Xn, #off]` (unsigned offset) -/
  | ldrq (t : VReg) (n : XReg) (off : Nat)
  /-- `STR Qt, [Xn, #off]` (unsigned offset) -/
  | strq (t : VReg) (n : XReg) (off : Nat)
  /-- `LD1 {Vt.T, …}, [Xn]` (multiple structures, 1–4 consecutive registers),
  or with `post`, `LD1 {…}, [Xn], #(16 * count)` (post-index) -/
  | ld1 (ts : List VReg) (arr : Arr) (n : XReg) (post : Bool)
  /-- `ST1 {Vt.T, …}, [Xn]` (multiple structures), or post-indexed -/
  | st1 (ts : List VReg) (arr : Arr) (n : XReg) (post : Bool)
  /-- `REV32 Vd.16B, Vn.16B` -/
  | rev32 (d n : VReg)
  /-- `ADD Vd.4S, Vn.4S, Vm.4S` -/
  | addv (d n m : VReg)
  /-- `MOV Vd.16B, Vn.16B` (alias of `ORR Vd.16B, Vn.16B, Vn.16B`) -/
  | movv (d n : VReg)
  /-- `SHA256H Qd, Qn, Vm.4S` -/
  | sha256h (d n m : VReg)
  /-- `SHA256H2 Qd, Qn, Vm.4S` -/
  | sha256h2 (d n m : VReg)
  /-- `SHA256SU0 Vd.4S, Vn.4S` -/
  | sha256su0 (d n : VReg)
  /-- `SHA256SU1 Vd.4S, Vn.4S, Vm.4S` -/
  | sha256su1 (d n m : VReg)
  /-- `ADR Xd, label` -/
  | adr (d : XReg) (label : String)
  /-- `ADD Xd, Xn, #imm` -/
  | addi (d n : XReg) (imm : Nat)
  /-- `SUB Xd, Xn, #imm` -/
  | subi (d n : XReg) (imm : Nat)
  /-- `SUBS Xd, Xn, #imm` (sets NZCV) -/
  | subsi (d n : XReg) (imm : Nat)
  /-- `MOV Xd, Xn` (alias of `ORR Xd, XZR, Xn`) -/
  | mov (d n : XReg)
  deriving DecidableEq, Repr

/-- Branch conditions: `b.<cond>` on the flags, and compare-and-branch. -/
inductive Cond
  | eq | ne | hs | lo | hi | ls
  /-- `CBZ Xt, label` -/
  | cbz (t : XReg)
  /-- `CBNZ Xt, label` -/
  | cbnz (t : XReg)
  deriving DecidableEq, Repr

namespace State

def getX (s : State) (r : XReg) : BitVec 64 := s.x.get r
def setX (s : State) (r : XReg) (v : BitVec 64) : State := { s with x := s.x.set r v }
def getV (s : State) (r : VReg) : BitVec 128 := s.v.get r
def setV (s : State) (r : VReg) (v : BitVec 128) : State := { s with v := s.v.set r v }

/-- Load a `w`-bit value (`w` a multiple of 8), faulting if not permitted. -/
def loadW (s : State) (w : Nat) (a : Addr) : Option (BitVec w) :=
  if InRegions (s.rd ++ s.wr) a (w / 8) then some (s.mem.readW a w) else none

/-- Store a `w`-bit value (`w` a multiple of 8), faulting if not permitted. -/
def storeW (s : State) {w : Nat} (a : Addr) (v : BitVec w) : Option State :=
  if InRegions s.wr a (w / 8) then some { s with mem := s.mem.writeW a v } else none

/-- The register transfers of `LD1 {Vt, …}, [a]`: register number `i` of the list
is loaded from `a + 16 * i`. -/
def ld1Regs (s : State) (a : Addr) (i : Nat) : List VReg → Option State
  | [] => some s
  | t :: ts => (s.loadW 128 (a + BitVec.ofNat 64 (16 * i))).bind fun x =>
    (s.setV t x).ld1Regs a (i + 1) ts

/-- The register transfers of `ST1 {Vt, …}, [a]`. -/
def st1Regs (s : State) (a : Addr) (i : Nat) : List VReg → Option State
  | [] => some s
  | t :: ts => (s.storeW (a + BitVec.ofNat 64 (16 * i)) (s.getV t)).bind fun s' =>
    s'.st1Regs a (i + 1) ts

end State

/-- The addresses accessed by `LD1`/`ST1` of the registers `ts` at `a`. -/
def ldstAddrs (a : Addr) (i : Nat) : List VReg → List Addr
  | [] => []
  | _ :: ts => (a + BitVec.ofNat 64 (16 * i)) :: ldstAddrs a (i + 1) ts

/-- `AddWithCarry(x, y, carry_in)` of the Arm ARM, returning the result and
the flags `(N, Z, C, V)`.  C is set iff the unsigned sum does not fit
(`UInt(result) != unsigned_sum`); V is set iff the signed sum does not fit
(`SInt(result) != signed_sum`), which happens exactly when both operands have
the same sign and the result's sign differs. -/
def addWithCarry (x y : BitVec 64) (carry : Bool) : BitVec 64 × Bool × Bool × Bool × Bool :=
  let usum := x.toNat + y.toNat + carry.toNat
  let r := BitVec.ofNat 64 usum
  (r, r.msb, r == 0, Nat.ble (2 ^ 64) usum, x.msb == y.msb && r.msb != x.msb)

/-- Instruction semantics. -/
def exec (i : Instr) (s : State) : Option State :=
  match i with
  | .ldrq t n off => (s.loadW 128 (s.getX n + BitVec.ofNat 64 off)).map fun x => s.setV t x
  | .strq t n off => s.storeW (s.getX n + BitVec.ofNat 64 off) (s.getV t)
  | .ld1 ts _ n post =>
    let a := s.getX n
    (s.ld1Regs a 0 ts).map fun s' =>
      if post then s'.setX n (a + BitVec.ofNat 64 (16 * ts.length)) else s'
  | .st1 ts _ n post =>
    let a := s.getX n
    (s.st1Regs a 0 ts).map fun s' =>
      if post then s'.setX n (a + BitVec.ofNat 64 (16 * ts.length)) else s'
  | .rev32 d n => some (s.setV d (rev32 (s.getV n)))
  | .addv d n m => some (s.setV d (vadd32 (s.getV n) (s.getV m)))
  | .movv d n => some (s.setV d (s.getV n))
  | .sha256h d n m => some (s.setV d (sha256hash (s.getV d) (s.getV n) (s.getV m) true))
  | .sha256h2 d n m => some (s.setV d (sha256hash (s.getV n) (s.getV d) (s.getV m) false))
  | .sha256su0 d n => some (s.setV d (sha256su0 (s.getV d) (s.getV n)))
  | .sha256su1 d n m => some (s.setV d (sha256su1 (s.getV d) (s.getV n) (s.getV m)))
  | .adr d l => some (s.setX d (s.labels l))
  | .addi d n imm => some (s.setX d (s.getX n + BitVec.ofNat 64 imm))
  | .subi d n imm => some (s.setX d (s.getX n - BitVec.ofNat 64 imm))
  | .subsi d n imm =>
    -- `(result, nzcv) = AddWithCarry(X[n], NOT(imm), '1')`
    let r := addWithCarry (s.getX n) (~~~(BitVec.ofNat 64 imm)) true
    some ({ s with nf := some r.2.1, zf := some r.2.2.1, cf := some r.2.2.2.1,
                   vf := some r.2.2.2.2 }.setX d r.1)
  | .mov d n => some (s.setX d (s.getX n))

/-- The memory addresses accessed by an instruction. -/
def addrs (i : Instr) (s : State) : List Addr :=
  match i with
  | .ldrq _ n off | .strq _ n off => [s.getX n + BitVec.ofNat 64 off]
  | .ld1 ts _ n _ | .st1 ts _ n _ => ldstAddrs (s.getX n) 0 ts
  | _ => []

/-- `ConditionHolds` for the modelled conditions, and compare-and-branch. -/
def evalCond (c : Cond) (s : State) : Option Bool :=
  match c with
  | .eq => s.zf
  | .ne => s.zf.map (!·)
  | .hs => s.cf
  | .lo => s.cf.map (!·)
  | .hi => do let c ← s.cf; let z ← s.zf; pure (c && !z)
  | .ls => do let c ← s.cf; let z ← s.zf; pure (!c || z)
  | .cbz t => some (s.getX t == 0)
  | .cbnz t => some (s.getX t != 0)

@[reducible] def isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := evalCond

abbrev Prog := CC.Prog isa

/-! ## The AAPCS64 calling convention -/

/-- The registers a function must preserve (AAPCS64 §6.1.1): `X19`–`X28`, the frame
pointer `X29`, the link register `X30` (so the function returns to its caller),
`SP`, and the low 64 bits `D8`–`D15` of `V8`–`V15`. -/
def CalleeSaved (s s' : State) : Prop :=
  s'.x.x19 = s.x.x19 ∧ s'.x.x20 = s.x.x20 ∧ s'.x.x21 = s.x.x21 ∧ s'.x.x22 = s.x.x22 ∧
  s'.x.x23 = s.x.x23 ∧ s'.x.x24 = s.x.x24 ∧ s'.x.x25 = s.x.x25 ∧ s'.x.x26 = s.x.x26 ∧
  s'.x.x27 = s.x.x27 ∧ s'.x.x28 = s.x.x28 ∧ s'.x.x29 = s.x.x29 ∧ s'.x.x30 = s.x.x30 ∧
  s'.sp = s.sp ∧
  s'.v.v8.setWidth 64 = s.v.v8.setWidth 64 ∧ s'.v.v9.setWidth 64 = s.v.v9.setWidth 64 ∧
  s'.v.v10.setWidth 64 = s.v.v10.setWidth 64 ∧ s'.v.v11.setWidth 64 = s.v.v11.setWidth 64 ∧
  s'.v.v12.setWidth 64 = s.v.v12.setWidth 64 ∧ s'.v.v13.setWidth 64 = s.v.v13.setWidth 64 ∧
  s'.v.v14.setWidth 64 = s.v.v14.setWidth 64 ∧ s'.v.v15.setWidth 64 = s.v.v15.setWidth 64

end CC.Arm
