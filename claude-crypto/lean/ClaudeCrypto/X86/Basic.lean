import ClaudeCrypto.Framework.Code
import ClaudeCrypto.Common.Lanes

/-!
# x86-64 machine model

A model of the subset of x86-64 used by our implementations.  This file is
part of the trusted computing base: each instruction's semantics here must
agree with the Intel SDM.  (They are additionally cross-checked against the
real CPU by the differential tests in `test/`.)

Modelling choices:
* Only CF, ZF, SF, OF are modelled.  Each is an `Option Bool`; `none` means
  "undefined" (as the SDM specifies for e.g. OF after a multi-bit rotate).
  Reading an undefined flag faults, so verified code never depends on one.
  PF and AF are not modelled at all, and no modelled instruction reads them.
* Writes to a 32-bit register zero the upper 32 bits (SDM Vol. 1 §3.4.1.1).
* Memory accesses must lie within the state's permitted regions: loads
  within `rd ++ wr`, stores within `wr`; otherwise the instruction faults.
-/

namespace CC.X86

inductive Reg
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr, Inhabited

structure Regs where
  rax : BitVec 64
  rcx : BitVec 64
  rdx : BitVec 64
  rbx : BitVec 64
  rsp : BitVec 64
  rbp : BitVec 64
  rsi : BitVec 64
  rdi : BitVec 64
  r8 : BitVec 64
  r9 : BitVec 64
  r10 : BitVec 64
  r11 : BitVec 64
  r12 : BitVec 64
  r13 : BitVec 64
  r14 : BitVec 64
  r15 : BitVec 64
  deriving DecidableEq, Repr

namespace Regs
def get (g : Regs) : Reg → BitVec 64
  | .rax => g.rax | .rcx => g.rcx | .rdx => g.rdx | .rbx => g.rbx
  | .rsp => g.rsp | .rbp => g.rbp | .rsi => g.rsi | .rdi => g.rdi
  | .r8 => g.r8 | .r9 => g.r9 | .r10 => g.r10 | .r11 => g.r11
  | .r12 => g.r12 | .r13 => g.r13 | .r14 => g.r14 | .r15 => g.r15

def set (g : Regs) (r : Reg) (v : BitVec 64) : Regs :=
  match r with
  | .rax => { g with rax := v } | .rcx => { g with rcx := v }
  | .rdx => { g with rdx := v } | .rbx => { g with rbx := v }
  | .rsp => { g with rsp := v } | .rbp => { g with rbp := v }
  | .rsi => { g with rsi := v } | .rdi => { g with rdi := v }
  | .r8 => { g with r8 := v } | .r9 => { g with r9 := v }
  | .r10 => { g with r10 := v } | .r11 => { g with r11 := v }
  | .r12 => { g with r12 := v } | .r13 => { g with r13 := v }
  | .r14 => { g with r14 := v } | .r15 => { g with r15 := v }
end Regs

/-- 256-bit vector registers (ymm0–ymm15). -/
inductive VReg
  | y0 | y1 | y2 | y3 | y4 | y5 | y6 | y7
  | y8 | y9 | y10 | y11 | y12 | y13 | y14 | y15
  deriving DecidableEq, Repr, Inhabited

structure VRegs where
  y0 : BitVec 256
  y1 : BitVec 256
  y2 : BitVec 256
  y3 : BitVec 256
  y4 : BitVec 256
  y5 : BitVec 256
  y6 : BitVec 256
  y7 : BitVec 256
  y8 : BitVec 256
  y9 : BitVec 256
  y10 : BitVec 256
  y11 : BitVec 256
  y12 : BitVec 256
  y13 : BitVec 256
  y14 : BitVec 256
  y15 : BitVec 256
  deriving DecidableEq, Repr

namespace VRegs
def get (g : VRegs) : VReg → BitVec 256
  | .y0 => g.y0 | .y1 => g.y1 | .y2 => g.y2 | .y3 => g.y3
  | .y4 => g.y4 | .y5 => g.y5 | .y6 => g.y6 | .y7 => g.y7
  | .y8 => g.y8 | .y9 => g.y9 | .y10 => g.y10 | .y11 => g.y11
  | .y12 => g.y12 | .y13 => g.y13 | .y14 => g.y14 | .y15 => g.y15

def set (g : VRegs) (r : VReg) (v : BitVec 256) : VRegs :=
  match r with
  | .y0 => { g with y0 := v } | .y1 => { g with y1 := v }
  | .y2 => { g with y2 := v } | .y3 => { g with y3 := v }
  | .y4 => { g with y4 := v } | .y5 => { g with y5 := v }
  | .y6 => { g with y6 := v } | .y7 => { g with y7 := v }
  | .y8 => { g with y8 := v } | .y9 => { g with y9 := v }
  | .y10 => { g with y10 := v } | .y11 => { g with y11 := v }
  | .y12 => { g with y12 := v } | .y13 => { g with y13 := v }
  | .y14 => { g with y14 := v } | .y15 => { g with y15 := v }
end VRegs

structure State where
  gpr : Regs
  vec : VRegs
  cf : Option Bool
  zf : Option Bool
  sf : Option Bool
  of : Option Bool
  mem : Mem
  /-- Regions the code may read (in addition to `wr`). -/
  rd : List Region
  /-- Regions the code may read and write. -/
  wr : List Region
  /-- Load addresses of the data labels (constant tables) of the module. -/
  labels : String → Addr

/-- Operand size. -/
inductive Sz | d | q
  deriving DecidableEq, Repr

/-- A memory operand `[base + index*scale + disp]`, or `[rip + label + disp]`
when `rip = some label` (then `base`/`index` are ignored). -/
structure MemOp where
  base : Reg := .rsp
  index : Option Reg := none
  scale : Nat := 1
  disp : Int := 0
  rip : Option String := none
  deriving DecidableEq, Repr

inductive Src
  | reg (r : Reg)
  /-- A 32-bit immediate (sign-extended for 64-bit operations). -/
  | imm (v : BitVec 32)
  | mem (m : MemOp)
  deriving DecidableEq, Repr

/-- A vector source operand. -/
inductive VSrc
  | reg (v : VReg)
  | mem (m : MemOp)
  deriving DecidableEq, Repr

inductive AluOp | add | adc | sub | sbb | and | or | xor | cmp | test
  deriving DecidableEq, Repr

inductive ShiftOp | ror | rol | shr | shl
  deriving DecidableEq, Repr

inductive Instr
  /-- `mov dst, src` (register, immediate or memory source) -/
  | mov (sz : Sz) (dst : Reg) (src : Src)
  /-- `mov [dst], src` -/
  | store (sz : Sz) (dst : MemOp) (src : Reg)
  /-- two-operand ALU instruction `op dst, src` -/
  | alu (op : AluOp) (sz : Sz) (dst : Reg) (src : Src)
  /-- `lea dst, [m]` -/
  | lea (sz : Sz) (dst : Reg) (m : MemOp)
  /-- `rorx dst, src, imm` (BMI2; flags unaffected) -/
  | rorx (sz : Sz) (dst src : Reg) (imm : Nat)
  /-- `andn dst, src1, src2` = `~src1 & src2` (BMI1) -/
  | andn (sz : Sz) (dst src1 : Reg) (src2 : Src)
  /-- shift/rotate by an immediate -/
  | shift (op : ShiftOp) (sz : Sz) (dst : Reg) (imm : Nat)
  | not (sz : Sz) (dst : Reg)
  /-- `movbe dst, [m]` load with byte swap -/
  | movbe (sz : Sz) (dst : Reg) (m : MemOp)
  | bswap (sz : Sz) (dst : Reg)
  | push (r : Reg)
  | pop (r : Reg)
  | inc (sz : Sz) (dst : Reg)
  | dec (sz : Sz) (dst : Reg)
  /-- `vmovdqu xmm, m128` (VEX: zeroes bits 128–255) -/
  | vload128 (dst : VReg) (m : MemOp)
  /-- `vmovdqu ymm, m256` -/
  | vload256 (dst : VReg) (m : MemOp)
  /-- `vmovdqu m256, ymm` -/
  | vstore256 (m : MemOp) (src : VReg)
  /-- `vinserti128 dst, src, m128, 1` -/
  | vinserti128hi (dst src : VReg) (m : MemOp)
  /-- `vbroadcasti128 dst, m128` -/
  | vbroadcasti128 (dst : VReg) (m : MemOp)
  /-- `vpshufb dst, src, ctl` (per 128-bit lane) -/
  | vpshufb (dst src ctl : VReg)
  /-- `vpaddd dst, src1, src2` (8 × 32-bit) -/
  | vpaddd (dst src1 : VReg) (src2 : VSrc)
  /-- `vpxor dst, src1, src2` -/
  | vpxor (dst src1 src2 : VReg)
  /-- `vpalignr dst, src1, src2, imm` (per 128-bit lane) -/
  | vpalignr (dst src1 src2 : VReg) (imm : Nat)
  /-- `vpsrld dst, src, imm` (8 × 32-bit logical right shift) -/
  | vpsrld (dst src : VReg) (imm : Nat)
  /-- `vpslld dst, src, imm` -/
  | vpslld (dst src : VReg) (imm : Nat)
  /-- `vpsrlq dst, src, imm` (4 × 64-bit logical right shift) -/
  | vpsrlq (dst src : VReg) (imm : Nat)
  /-- `vpshufd dst, src, imm` (per 128-bit lane) -/
  | vpshufd (dst src : VReg) (imm : Nat)
  | vzeroupper
  deriving DecidableEq, Repr

/-- Branch conditions (`jcc` suffixes). -/
inductive Cond | e | ne | b | ae | be | a
  deriving DecidableEq, Repr

def Sz.bits : Sz → Nat | .d => 32 | .q => 64

namespace State

@[simp] def getReg (s : State) (r : Reg) : BitVec 64 := s.gpr.get r
@[simp] def setReg (s : State) (r : Reg) (v : BitVec 64) : State := { s with gpr := s.gpr.set r v }

/-- The low `w` bits of a register. -/
def readW (s : State) (w : Nat) (r : Reg) : BitVec w := (s.gpr.get r).setWidth w

/-- Write a `w`-bit value (`w ∈ {32, 64}`) to a register; 32-bit writes zero-extend. -/
def writeW (s : State) {w : Nat} (r : Reg) (v : BitVec w) : State := s.setReg r (v.setWidth 64)

def ea (s : State) (m : MemOp) : Addr :=
  match m.rip with
  | some l => s.labels l + BitVec.ofInt 64 m.disp
  | none =>
    match m.index with
    | none => s.getReg m.base + BitVec.ofInt 64 m.disp
    | some i => s.getReg m.base + s.getReg i * BitVec.ofNat 64 m.scale + BitVec.ofInt 64 m.disp

@[simp] def getV (s : State) (v : VReg) : BitVec 256 := s.vec.get v
@[simp] def setV (s : State) (v : VReg) (x : BitVec 256) : State := { s with vec := s.vec.set v x }

/-- Load `n` bytes, faulting if not permitted. -/
def load (s : State) (a : Addr) (n : Nat) : Option (BitVec (8 * n)) :=
  if InRegions (s.rd ++ s.wr) a n then some (s.mem.read a n) else none

/-- Store `n` bytes, faulting if not permitted. -/
def store (s : State) (a : Addr) (n : Nat) (v : BitVec (8 * n)) : Option State :=
  if InRegions s.wr a n then some { s with mem := s.mem.write a n v } else none

/-- Load a `w`-bit value (`w` a multiple of 8). -/
def loadW (s : State) (w : Nat) (a : Addr) : Option (BitVec w) :=
  if InRegions (s.rd ++ s.wr) a (w / 8) then some (s.mem.readW a w) else none

def storeW (s : State) {w : Nat} (a : Addr) (v : BitVec w) : Option State :=
  if InRegions s.wr a (w / 8) then some { s with mem := s.mem.writeW a v } else none

end State

/-- Read a `w`-bit source operand.  Immediates are sign-extended from 32 bits. -/
def readSrc (s : State) (w : Nat) : Src → Option (BitVec w)
  | .reg r => some (s.readW w r)
  | .imm v => some (v.signExtend w)
  | .mem m => s.loadW w (s.ea m)

def srcAddrs (s : State) : Src → List Addr
  | .mem m => [s.ea m]
  | _ => []

def setFlags (s : State) (cf of zf sf : Option Bool) : State :=
  { s with cf := cf, of := of, zf := zf, sf := sf }

/-- Flags after an arithmetic/logic result `r` with the given carry and overflow. -/
def arithFlags {w : Nat} (s : State) (r : BitVec w) (c o : Bool) : State :=
  setFlags s (some c) (some o) (some (r == 0)) (some r.msb)

/-- Signed overflow of `a + b + c`. -/
def addOverflow {w : Nat} (a b r : BitVec w) : Bool := a.msb == b.msb && r.msb != a.msb
/-- Signed overflow of `a - b - c`. -/
def subOverflow {w : Nat} (a b r : BitVec w) : Bool := a.msb != b.msb && r.msb != a.msb

def execAlu (w : Nat) (op : AluOp) (dst : Reg) (src : Src) (s : State) : Option State :=
  (readSrc s w src).bind fun b =>
  let a := s.readW w dst
  match op with
  | .add => let r := a + b
    some ((arithFlags s r (Nat.ble (2 ^ w) (a.toNat + b.toNat)) (addOverflow a b r)).writeW dst r)
  | .adc => s.cf.map fun c =>
    let r := a + b + (BitVec.ofBool c).setWidth w
    (arithFlags s r (Nat.ble (2 ^ w) (a.toNat + b.toNat + c.toNat)) (addOverflow a b r)).writeW dst r
  | .sub => let r := a - b
    some ((arithFlags s r (Nat.blt a.toNat b.toNat) (subOverflow a b r)).writeW dst r)
  | .sbb => s.cf.map fun c =>
    let r := a - b - (BitVec.ofBool c).setWidth w
    (arithFlags s r (Nat.blt a.toNat (b.toNat + c.toNat)) (subOverflow a b r)).writeW dst r
  | .cmp => let r := a - b
    some (arithFlags s r (Nat.blt a.toNat b.toNat) (subOverflow a b r))
  | .and => let r := a &&& b; some ((arithFlags s r false false).writeW dst r)
  | .or => let r := a ||| b; some ((arithFlags s r false false).writeW dst r)
  | .xor => let r := a ^^^ b; some ((arithFlags s r false false).writeW dst r)
  | .test => let r := a &&& b; some (arithFlags s r false false)

/-- Shifts and rotates by an immediate count.  The count is masked to 5 (32-bit)
or 6 (64-bit) bits; a zero count changes nothing.  OF is only defined for a
count of 1. -/
def execShift (w : Nat) (op : ShiftOp) (dst : Reg) (n : Nat) (s : State) : Option State :=
  let cnt := n % w
  if cnt = 0 then some s else
  let v := s.readW w dst
  match op with
  | .ror => let r := v.rotateRight cnt
    some ({ s with cf := some r.msb,
                   of := if cnt = 1 then some (r.msb != r.getLsbD (w - 2)) else none }.writeW dst r)
  | .rol => let r := v.rotateLeft cnt
    some ({ s with cf := some (r.getLsbD 0),
                   of := if cnt = 1 then some (r.msb != r.getLsbD 0) else none }.writeW dst r)
  | .shr => let r := v >>> cnt
    some ((setFlags s (some (v.getLsbD (cnt - 1))) (if cnt = 1 then some v.msb else none)
      (some (r == 0)) (some r.msb)).writeW dst r)
  | .shl => let r := v <<< cnt
    some ((setFlags s (some (v.getLsbD (w - cnt)))
      (if cnt = 1 then some (r.msb != v.getLsbD (w - cnt)) else none)
      (some (r == 0)) (some r.msb)).writeW dst r)

/-- Reverse the byte order of a 32- or 64-bit value. -/
def bswap32 (x : BitVec 32) : BitVec 32 :=
  x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8
def bswap64 (x : BitVec 64) : BitVec 64 :=
  x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8 ++
  x.extractLsb' 32 8 ++ x.extractLsb' 40 8 ++ x.extractLsb' 48 8 ++ x.extractLsb' 56 8

/-! ### SIMD helpers (AVX2, VEX.256 forms) -/

/-- The byte shuffle of `vpshufb` on one 128-bit lane. -/
def pshufb128 (x c : BitVec 128) : BitVec 128 :=
  BitVec.lanes 16 fun i =>
    let ci := BitVec.lane 8 c i
    if ci.msb then 0 else BitVec.lane 8 x (ci.toNat % 16)

def vpshufbV (x c : BitVec 256) : BitVec 256 :=
  BitVec.lanes 2 fun L => pshufb128 (BitVec.lane 128 x L) (BitVec.lane 128 c L)

def vpadddV (x y : BitVec 256) : BitVec 256 :=
  BitVec.lanes 8 fun i => BitVec.lane 32 x i + BitVec.lane 32 y i

/-- `vpalignr` on one 128-bit lane: bytes `imm … imm+15` of `hi:lo`. -/
def palignr128 (hi lo : BitVec 128) (imm : Nat) : BitVec 128 :=
  ((hi ++ lo) >>> (8 * imm)).setWidth 128

def vpalignrV (x y : BitVec 256) (imm : Nat) : BitVec 256 :=
  BitVec.lanes 2 fun L => palignr128 (BitVec.lane 128 x L) (BitVec.lane 128 y L) imm

def vpsrldV (x : BitVec 256) (n : Nat) : BitVec 256 :=
  BitVec.lanes 8 fun i => if n > 31 then 0 else BitVec.lane 32 x i >>> n

def vpslldV (x : BitVec 256) (n : Nat) : BitVec 256 :=
  BitVec.lanes 8 fun i => if n > 31 then 0 else BitVec.lane 32 x i <<< n

def vpsrlqV (x : BitVec 256) (n : Nat) : BitVec 256 :=
  BitVec.lanes 4 fun i => if n > 63 then 0 else BitVec.lane 64 x i >>> n

def pshufd128 (x : BitVec 128) (imm : Nat) : BitVec 128 :=
  BitVec.lanes 4 fun j => BitVec.lane 32 x ((imm / 4 ^ j) % 4)

def vpshufdV (x : BitVec 256) (imm : Nat) : BitVec 256 :=
  BitVec.lanes 2 fun L => pshufd128 (BitVec.lane 128 x L) imm

/-- Clear bits 128–255 of every ymm register. -/
def zeroUpper (v : VRegs) : VRegs :=
  let z : BitVec 256 → BitVec 256 := fun x => (x.setWidth 128).setWidth 256
  ⟨z v.y0, z v.y1, z v.y2, z v.y3, z v.y4, z v.y5, z v.y6, z v.y7,
   z v.y8, z v.y9, z v.y10, z v.y11, z v.y12, z v.y13, z v.y14, z v.y15⟩

def readVSrc (s : State) : VSrc → Option (BitVec 256)
  | .reg v => some (s.getV v)
  | .mem m => s.loadW 256 (s.ea m)

/-- Semantics of the SIMD instructions (independent of the operand size). -/
def execV (i : Instr) (s : State) : Option State :=
  match i with
  | .vload128 dst m => (s.loadW 128 (s.ea m)).map fun v => s.setV dst (v.setWidth 256)
  | .vload256 dst m => (s.loadW 256 (s.ea m)).map fun v => s.setV dst v
  | .vstore256 m src => s.storeW (s.ea m) (s.getV src)
  | .vinserti128hi dst src m => (s.loadW 128 (s.ea m)).map fun v =>
      s.setV dst (v ++ (s.getV src).setWidth 128)
  | .vbroadcasti128 dst m => (s.loadW 128 (s.ea m)).map fun v => s.setV dst (v ++ v)
  | .vpshufb dst src ctl => some (s.setV dst (vpshufbV (s.getV src) (s.getV ctl)))
  | .vpaddd dst src1 src2 => (readVSrc s src2).map fun y => s.setV dst (vpadddV (s.getV src1) y)
  | .vpxor dst src1 src2 => some (s.setV dst (s.getV src1 ^^^ s.getV src2))
  | .vpalignr dst src1 src2 imm => some (s.setV dst (vpalignrV (s.getV src1) (s.getV src2) imm))
  | .vpsrld dst src n => some (s.setV dst (vpsrldV (s.getV src) n))
  | .vpslld dst src n => some (s.setV dst (vpslldV (s.getV src) n))
  | .vpsrlq dst src n => some (s.setV dst (vpsrlqV (s.getV src) n))
  | .vpshufd dst src imm => some (s.setV dst (vpshufdV (s.getV src) imm))
  | .vzeroupper => some { s with vec := zeroUpper s.vec }
  | _ => none

/-- Instruction semantics at a fixed width `w ∈ {32, 64}`. -/
def execW (w : Nat) (bswap : BitVec w → BitVec w) (i : Instr) (s : State) : Option State :=
  match i with
  | .mov _ dst src => (readSrc s w src).map fun v => s.writeW dst v
  | .store _ m src => s.storeW (s.ea m) (s.readW w src)
  | .alu op _ dst src => execAlu w op dst src s
  | .lea _ dst m => some (s.writeW dst ((s.ea m).setWidth w))
  | .rorx _ dst src n => some (s.writeW dst ((s.readW w src).rotateRight (n % w)))
  | .andn _ dst s1 s2 => (readSrc s w s2).map fun b =>
    let r := ~~~(s.readW w s1) &&& b
    (arithFlags s r false false).writeW dst r
  | .shift op _ dst n => execShift w op dst n s
  | .not _ dst => some (s.writeW dst (~~~(s.readW w dst)))
  | .movbe _ dst m => (s.loadW w (s.ea m)).map fun v => s.writeW dst (bswap v)
  | .bswap _ dst => some (s.writeW dst (bswap (s.readW w dst)))
  | .inc _ dst =>
    let v := s.readW w dst
    let r := v + 1
    some ({ s with of := some (r.msb && !v.msb), zf := some (r == 0), sf := some r.msb }.writeW dst r)
  | .dec _ dst =>
    let v := s.readW w dst
    let r := v - 1
    some ({ s with of := some (!r.msb && v.msb), zf := some (r == 0), sf := some r.msb }.writeW dst r)
  | .push r =>
    let sp := s.getReg .rsp - 8
    (s.storeW sp (s.getReg r)).map fun s' => s'.setReg .rsp sp
  | .pop r => (s.loadW 64 (s.getReg .rsp)).map fun v =>
    (s.setReg .rsp (s.getReg .rsp + 8)).setReg r v
  | _ => execV i s

def Instr.sz : Instr → Sz
  | .mov sz .. | .store sz .. | .alu _ sz .. | .lea sz .. | .rorx sz .. | .andn sz ..
  | .shift _ sz .. | .not sz .. | .movbe sz .. | .bswap sz .. | .inc sz .. | .dec sz .. => sz
  | _ => .q

def exec (i : Instr) (s : State) : Option State :=
  match i.sz with
  | .d => execW 32 bswap32 i s
  | .q => execW 64 bswap64 i s

def addrs (i : Instr) (s : State) : List Addr :=
  match i with
  | .mov _ _ src | .alu _ _ _ src | .andn _ _ _ src => srcAddrs s src
  | .store _ m _ | .movbe _ _ m => [s.ea m]
  | .push _ => [s.getReg .rsp - 8]
  | .pop _ => [s.getReg .rsp]
  | .vload128 _ m | .vload256 _ m | .vstore256 m _ | .vinserti128hi _ _ m | .vbroadcasti128 _ m =>
    [s.ea m]
  | .vpaddd _ _ (.mem m) => [s.ea m]
  | _ => []

def evalCond (c : Cond) (s : State) : Option Bool :=
  match c with
  | .e => s.zf
  | .ne => s.zf.map (!·)
  | .b => s.cf
  | .ae => s.cf.map (!·)
  | .be => do let c ← s.cf; let z ← s.zf; pure (c || z)
  | .a => do let c ← s.cf; let z ← s.zf; pure (!c && !z)

@[reducible] def isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := evalCond

abbrev Prog := CC.Prog isa

end CC.X86
