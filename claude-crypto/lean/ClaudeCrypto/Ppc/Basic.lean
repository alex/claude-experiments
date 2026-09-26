import ClaudeCrypto.Framework.Code

/-!
# ppc64le machine model

A model of the subset of the 64-bit Power ISA (version 2.07, i.e. POWER8;
little-endian mode, problem state) used by our implementations.  This file is
part of the trusted computing base: each instruction's semantics here must
agree with the *Power ISA* book (Version 2.07B / 3.0B / 3.1).  The ISA
pseudocode we transcribe is quoted in the comments.  (All modelled vector,
VSX, load/store and compare instructions are additionally cross-checked
against QEMU by `test/ppc_insn_test.c` + `test/PpcInsnCheck.lean`, and the
complete generated function by the differential tests in `test/`; see
`test/run_ppc64le.sh`.)

## Bit and element numbering

The Power ISA numbers bits *from the most significant end*: bit 0 of a
128-bit vector register is its most significant bit, `word[0]` (bits 0:31) is
its most significant word, `byte[0]` its most significant byte.  We represent
registers as Lean `BitVec`s, whose bit 0 is the *least* significant, so ISA
`word[i]` of a vector is `x.extractLsb' (96 - 32 * i) 32` (`word x i` below),
and the ISA concatenation `a || b` (with `a` most significant) is Lean's
`a ++ b`.  All vector instructions are defined by the ISA in terms of this
register numbering, independently of the endian mode; only *memory accesses*
depend on the endian mode.

## Little-endian mode

In little-endian mode `MEM(EA, n)` accesses `n` bytes as a little-endian
integer: the byte at `EA` is the least significant.  That is exactly
`Mem.readW`/`Mem.writeW`.  Consequently `lxvw4x` loads the word at `EA`
(decoded little-endian) into ISA `word[0]` (the *most significant* word of
the register), the word at `EA + 4` into `word[1]`, and so on.

## Modelling choices

* State: `GPR0`–`GPR31`; the 32 vector registers `VR0`–`VR31` (which are
  `VSR32`–`VSR63`); `VSR0`–`VSR31` (whose most significant doublewords are
  the floating-point registers `FPR0`–`FPR31`), which no modelled
  instruction touches; the link register `LR`; the `LT`, `GT` and `EQ` bits of
  CR field 0; CR fields 1–7; memory; the permitted memory regions; and the
  (link-time) addresses of the data labels of the program.
* Each CR0 bit is an `Option Bool`; `none` means "unknown".  Reading an
  unknown bit faults, so verified code never depends on one.  `CR0.SO` (a copy
  of `XER.SO`) and `XER` are not modelled: no modelled instruction reads them,
  and the only modelled writer of `CR0.SO` is `cmpli`.
* VSX instructions (`lxvw4x`, `stxvw4x`, `xxpermdi`) are only modelled with
  operands `VSR32`–`VSR63`, i.e. the vector registers `VR0`–`VR31`; the
  printer emits the VSR number `32 + n` for `VRn`.
* Memory accesses must lie within the state's permitted regions: loads
  within `rd ++ wr`, stores within `wr` (one check for all 16 bytes of an
  `lxvw4x`/`stxvw4x`, which is stricter than the ISA's four word accesses);
  otherwise the instruction faults.  Alignment is not modelled: `lxvw4x` and
  `stxvw4x` permit arbitrary alignment.
* The block function counts its blocks up from `-n` to 0 (`neg` once, then
  `addi r5,r5,1`), so only non-negative `addi` immediates are used.
* Immediate operands are unrestricted numbers in the model; the assembler
  rejects any that are not encodable (e.g. `SH > 15` for `vsldoi`, a `SIX`
  field wider than 4 bits, `SI` outside `[-2^15, 2^15)`), so the emitted code
  is exactly the modelled code.
* `adr rt, label` is a *pseudo-instruction* (the one trusted multi-instruction
  macro, see `Ppc/Print.lean`): it expands to the position-independent
  sequence `mflr 0; bcl 20,31,1f; 1: mflr rt; mtlr 0; addis rt,rt,(label-1b)@ha;
  addi rt,rt,(label-1b)@l` (as in OpenSSL's `LPICmeup`).  Its effect is
  `GPR[0] ← LR; GPR[rt] ← address of label`; `LR` is restored.  It faults for
  `rt ∈ {r0, r1}` (with `rt = r0` the sequence would clobber `LR`; `r1` is the
  stack pointer).
-/

namespace CC.Ppc

inductive GReg
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  | r16 | r17 | r18 | r19 | r20 | r21 | r22 | r23
  | r24 | r25 | r26 | r27 | r28 | r29 | r30 | r31
  deriving DecidableEq, Repr, Inhabited

structure GRegs where
  r0 : BitVec 64
  r1 : BitVec 64
  r2 : BitVec 64
  r3 : BitVec 64
  r4 : BitVec 64
  r5 : BitVec 64
  r6 : BitVec 64
  r7 : BitVec 64
  r8 : BitVec 64
  r9 : BitVec 64
  r10 : BitVec 64
  r11 : BitVec 64
  r12 : BitVec 64
  r13 : BitVec 64
  r14 : BitVec 64
  r15 : BitVec 64
  r16 : BitVec 64
  r17 : BitVec 64
  r18 : BitVec 64
  r19 : BitVec 64
  r20 : BitVec 64
  r21 : BitVec 64
  r22 : BitVec 64
  r23 : BitVec 64
  r24 : BitVec 64
  r25 : BitVec 64
  r26 : BitVec 64
  r27 : BitVec 64
  r28 : BitVec 64
  r29 : BitVec 64
  r30 : BitVec 64
  r31 : BitVec 64

namespace GRegs
def get (g : GRegs) : GReg → BitVec 64
  | .r0 => g.r0 | .r1 => g.r1 | .r2 => g.r2 | .r3 => g.r3
  | .r4 => g.r4 | .r5 => g.r5 | .r6 => g.r6 | .r7 => g.r7
  | .r8 => g.r8 | .r9 => g.r9 | .r10 => g.r10 | .r11 => g.r11
  | .r12 => g.r12 | .r13 => g.r13 | .r14 => g.r14 | .r15 => g.r15
  | .r16 => g.r16 | .r17 => g.r17 | .r18 => g.r18 | .r19 => g.r19
  | .r20 => g.r20 | .r21 => g.r21 | .r22 => g.r22 | .r23 => g.r23
  | .r24 => g.r24 | .r25 => g.r25 | .r26 => g.r26 | .r27 => g.r27
  | .r28 => g.r28 | .r29 => g.r29 | .r30 => g.r30 | .r31 => g.r31

def set (g : GRegs) (r : GReg) (v : BitVec 64) : GRegs :=
  match r with
  | .r0 => { g with r0 := v } | .r1 => { g with r1 := v }
  | .r2 => { g with r2 := v } | .r3 => { g with r3 := v }
  | .r4 => { g with r4 := v } | .r5 => { g with r5 := v }
  | .r6 => { g with r6 := v } | .r7 => { g with r7 := v }
  | .r8 => { g with r8 := v } | .r9 => { g with r9 := v }
  | .r10 => { g with r10 := v } | .r11 => { g with r11 := v }
  | .r12 => { g with r12 := v } | .r13 => { g with r13 := v }
  | .r14 => { g with r14 := v } | .r15 => { g with r15 := v }
  | .r16 => { g with r16 := v } | .r17 => { g with r17 := v }
  | .r18 => { g with r18 := v } | .r19 => { g with r19 := v }
  | .r20 => { g with r20 := v } | .r21 => { g with r21 := v }
  | .r22 => { g with r22 := v } | .r23 => { g with r23 := v }
  | .r24 => { g with r24 := v } | .r25 => { g with r25 := v }
  | .r26 => { g with r26 := v } | .r27 => { g with r27 := v }
  | .r28 => { g with r28 := v } | .r29 => { g with r29 := v }
  | .r30 => { g with r30 := v } | .r31 => { g with r31 := v }
end GRegs

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

/-! ## Vector elements (ISA numbering: element 0 is the most significant) -/

/-- `VR.word[i]`: ISA bits `32i : 32i+31` of a 128-bit register (`word[0]` is the
most significant word). -/
def word (x : BitVec 128) (i : Nat) : BitVec 32 := x.extractLsb' (96 - 32 * i) 32

/-- `VR.dword[i]`: ISA bits `64i : 64i+63` (`dword[0]` is the most significant). -/
def dword (x : BitVec 128) (i : Nat) : BitVec 64 := x.extractLsb' (64 - 64 * i) 64

/-- `VR.byte[i]` of a `8n`-bit value: ISA bits `8i : 8i+7` (`byte[0]` is the most
significant byte). -/
def byteAt {n : Nat} (x : BitVec (8 * n)) (i : Nat) : BitVec 8 := x.extractLsb' (8 * (n - 1 - i)) 8

/-- `vadduwm VRT,VRA,VRB` (Vector Add Unsigned Word Modulo):
```
do i = 0 to 3
   VR[VRT].word[i] ← VR[VRA].word[i] + VR[VRB].word[i]    (mod 2^32)
```
-/
def vadduwm (a b : BitVec 128) : BitVec 128 :=
  (word a 0 + word b 0) ++ (word a 1 + word b 1) ++ (word a 2 + word b 2) ++ (word a 3 + word b 3)

/-- `vsel VRT,VRA,VRB,VRC` (Vector Select):
```
do i = 0 to 127
   if VR[VRC].bit[i] = 0 then VR[VRT].bit[i] ← VR[VRA].bit[i]
                         else VR[VRT].bit[i] ← VR[VRB].bit[i]
```
-/
def vsel (a b c : BitVec 128) : BitVec 128 := (a &&& ~~~c) ||| (b &&& c)

/-- `vsldoi VRT,VRA,VRB,SHB` (Vector Shift Left Double by Octet Immediate):
```
VR[VRT] ← (VR[VRA] || VR[VRB]).byte[SHB : SHB+15]
```
i.e. ISA bits `8·SHB : 8·SHB+127` of the 256-bit concatenation (valid for `SHB ≤ 15`). -/
def vsldoi (a b : BitVec 128) (sh : Nat) : BitVec 128 := (a ++ b).extractLsb' (128 - 8 * sh) 128

/-- `vperm VRT,VRA,VRB,VRC` (Vector Permute):
```
temp.bit[0:255] ← VR[VRA] || VR[VRB]
do i = 0 to 15
   index ← VR[VRC].byte[i].bit[3:7]
   VR[VRT].byte[i] ← temp.byte[index]
```
(`bit[3:7]` of a byte are its five least significant bits.) -/
def vperm (a b c : BitVec 128) : BitVec 128 :=
  let temp : BitVec (8 * 32) := a ++ b
  let r (i : Nat) : BitVec 8 := byteAt temp ((byteAt (n := 16) c i).toNat % 32)
  r 0 ++ r 1 ++ r 2 ++ r 3 ++ r 4 ++ r 5 ++ r 6 ++ r 7 ++
    r 8 ++ r 9 ++ r 10 ++ r 11 ++ r 12 ++ r 13 ++ r 14 ++ r 15

/-- `vmrghw VRT,VRA,VRB` (Vector Merge High Word):
```
do i = 0 to 1
   VR[VRT].word[2i]   ← VR[VRA].word[i]
   VR[VRT].word[2i+1] ← VR[VRB].word[i]
```
-/
def vmrghw (a b : BitVec 128) : BitVec 128 := word a 0 ++ word b 0 ++ word a 1 ++ word b 1

/-- `xxpermdi XT,XA,XB,DM` (VSX Permute Doubleword Immediate):
```
VSR[XT] ← (DM.bit[0] = 0 ? VSR[XA].dword[0] : VSR[XA].dword[1]) ||
          (DM.bit[1] = 0 ? VSR[XB].dword[0] : VSR[XB].dword[1])
```
(`DM` is a 2-bit field; `DM.bit[0]` is its most significant bit.) -/
def xxpermdi (a b : BitVec 128) (dm : Nat) : BitVec 128 :=
  (if dm.testBit 1 then dword a 1 else dword a 0) ++ (if dm.testBit 0 then dword b 1 else dword b 0)

/-- `vshasigmaw VRT,VRA,ST,SIX` (Vector SHA-256 Sigma Word):
```
do i = 0 to 3
   src ← VR[VRA].word[i]
   if ST=0 & SIX.bit[i]=0 then   // SHA-256 σ0 function
      VR[VRT].word[i] ← (src >>> 7) ^ (src >>> 18) ^ (src >> 3)
   if ST=0 & SIX.bit[i]=1 then   // SHA-256 σ1 function
      VR[VRT].word[i] ← (src >>> 17) ^ (src >>> 19) ^ (src >> 10)
   if ST=1 & SIX.bit[i]=0 then   // SHA-256 Σ0 function
      VR[VRT].word[i] ← (src >>> 2) ^ (src >>> 13) ^ (src >>> 22)
   if ST=1 & SIX.bit[i]=1 then   // SHA-256 Σ1 function
      VR[VRT].word[i] ← (src >>> 6) ^ (src >>> 11) ^ (src >>> 25)
```
(`>>>` rotates right, `>>` shifts right; `SIX` is a 4-bit field and
`SIX.bit[0]` its most significant bit.) -/
def shaSigmaWord (st sixBit : Bool) (src : BitVec 32) : BitVec 32 :=
  match st, sixBit with
  | false, false => src.rotateRight 7 ^^^ src.rotateRight 18 ^^^ src >>> 3
  | false, true => src.rotateRight 17 ^^^ src.rotateRight 19 ^^^ src >>> 10
  | true, false => src.rotateRight 2 ^^^ src.rotateRight 13 ^^^ src.rotateRight 22
  | true, true => src.rotateRight 6 ^^^ src.rotateRight 11 ^^^ src.rotateRight 25

def vshasigmaw (x : BitVec 128) (st : Bool) (six : Nat) : BitVec 128 :=
  shaSigmaWord st (six.testBit 3) (word x 0) ++ shaSigmaWord st (six.testBit 2) (word x 1) ++
    shaSigmaWord st (six.testBit 1) (word x 2) ++ shaSigmaWord st (six.testBit 0) (word x 3)

/-! ## Machine state -/

structure State where
  g : GRegs
  v : VRegs
  /-- `VSR0`–`VSR31` (`FPRn` is `VSR[n].dword[0]`); no modelled instruction accesses them. -/
  vsr : Fin 32 → BitVec 128
  /-- The link register. -/
  lr : BitVec 64
  /-- The `LT`, `GT` and `EQ` bits of CR field 0. -/
  lt : Option Bool
  gt : Option Bool
  eq : Option Bool
  /-- CR fields 1–7 (CR1 most significant); no modelled instruction writes them. -/
  cr1to7 : BitVec 28
  mem : Mem
  /-- Regions the code may read (in addition to `wr`). -/
  rd : List Region
  /-- Regions the code may read and write. -/
  wr : List Region
  /-- The address of each data label of the program (fixed at link time). -/
  labels : String → Addr

inductive Instr
  /-- `lxvw4x XT,RA,RB` (Load VSX Vector Word*4 Indexed), `XT = 32 + t` -/
  | lxvw4x (t : VReg) (ra rb : GReg)
  /-- `stxvw4x XS,RA,RB` (Store VSX Vector Word*4 Indexed), `XS = 32 + s` -/
  | stxvw4x (s : VReg) (ra rb : GReg)
  /-- `vadduwm VRT,VRA,VRB` -/
  | vadduwm (t a b : VReg)
  /-- `vxor VRT,VRA,VRB` -/
  | vxor (t a b : VReg)
  /-- `vor VRT,VRA,VRB` -/
  | vor (t a b : VReg)
  /-- `vsel VRT,VRA,VRB,VRC` -/
  | vsel (t a b c : VReg)
  /-- `vperm VRT,VRA,VRB,VRC` -/
  | vperm (t a b c : VReg)
  /-- `vsldoi VRT,VRA,VRB,SHB` -/
  | vsldoi (t a b : VReg) (sh : Nat)
  /-- `vmrghw VRT,VRA,VRB` -/
  | vmrghw (t a b : VReg)
  /-- `xxpermdi XT,XA,XB,DM` with `XT = 32 + t`, `XA = 32 + a`, `XB = 32 + b` -/
  | xxpermdi (t a b : VReg) (dm : Nat)
  /-- `vshasigmaw VRT,VRA,ST,SIX` -/
  | vshasigmaw (t a : VReg) (st : Bool) (six : Nat)
  /-- `addi RT,RA,SI` (`li RT,SI` when `RA = 0`) -/
  | addi (rt ra : GReg) (si : Int)
  /-- `neg RT,RA` -/
  | neg (rt ra : GReg)
  /-- `cmpli 0,1,RA,UI` (`cmpldi cr0,RA,UI`) -/
  | cmpldi (ra : GReg) (ui : Nat)
  /-- The address of a data label (pseudo-instruction, see the module doc). -/
  | adr (rt : GReg) (label : String)
  deriving DecidableEq, Repr

/-- Branch conditions on CR0 (`bc 12,2,target` = `beq`, `bc 4,2,target` = `bne`). -/
inductive Cond
  | eq | ne
  deriving DecidableEq, Repr

namespace State

def getG (s : State) (r : GReg) : BitVec 64 := s.g.get r
def setG (s : State) (r : GReg) (v : BitVec 64) : State := { s with g := s.g.set r v }
def getV (s : State) (r : VReg) : BitVec 128 := s.v.get r
def setV (s : State) (r : VReg) (v : BitVec 128) : State := { s with v := s.v.set r v }

/-- `(RA|0)`: the contents of `GPR[RA]`, or `0` if `RA = 0`. -/
def raOr0 (s : State) (ra : GReg) : BitVec 64 :=
  match ra with
  | .r0 => 0
  | _ => s.getG ra

/-- The effective address of an X-form access: `EA ← (RA|0) + (RB)`. -/
def ea (s : State) (ra rb : GReg) : Addr := s.raOr0 ra + s.getG rb

end State

/-- Instruction semantics. -/
def exec (i : Instr) (s : State) : Option State :=
  match i with
  | .lxvw4x t ra rb =>
    -- VSR[XT].word[0] ← MEM(EA, 4); word[1] ← MEM(EA+4, 4); word[2] ← MEM(EA+8, 4);
    -- word[3] ← MEM(EA+12, 4)
    let ea := s.ea ra rb
    if InRegions (s.rd ++ s.wr) ea 16 then
      some (s.setV t (s.mem.readW ea 32 ++ s.mem.readW (ea + 4) 32 ++ s.mem.readW (ea + 8) 32 ++
        s.mem.readW (ea + 12) 32))
    else none
  | .stxvw4x x ra rb =>
    -- MEM(EA, 4) ← VSR[XS].word[0]; MEM(EA+4, 4) ← word[1]; MEM(EA+8, 4) ← word[2];
    -- MEM(EA+12, 4) ← word[3]
    let ea := s.ea ra rb
    let v := s.getV x
    if InRegions s.wr ea 16 then
      some { s with mem := (((s.mem.writeW ea (word v 0)).writeW (ea + 4) (word v 1)).writeW (ea + 8)
        (word v 2)).writeW (ea + 12) (word v 3) }
    else none
  | .vadduwm t a b => some (s.setV t (vadduwm (s.getV a) (s.getV b)))
  -- VR[VRT] ← VR[VRA] ^ VR[VRB]
  | .vxor t a b => some (s.setV t (s.getV a ^^^ s.getV b))
  -- VR[VRT] ← VR[VRA] | VR[VRB]
  | .vor t a b => some (s.setV t (s.getV a ||| s.getV b))
  | .vsel t a b c => some (s.setV t (vsel (s.getV a) (s.getV b) (s.getV c)))
  | .vperm t a b c => some (s.setV t (vperm (s.getV a) (s.getV b) (s.getV c)))
  | .vsldoi t a b sh => some (s.setV t (vsldoi (s.getV a) (s.getV b) sh))
  | .vmrghw t a b => some (s.setV t (vmrghw (s.getV a) (s.getV b)))
  | .xxpermdi t a b dm => some (s.setV t (xxpermdi (s.getV a) (s.getV b) dm))
  | .vshasigmaw t a st six => some (s.setV t (vshasigmaw (s.getV a) st six))
  -- GPR[RT] ← (RA|0) + EXTS(SI)
  | .addi rt ra si => some (s.setG rt (s.raOr0 ra + BitVec.ofInt 64 si))
  -- GPR[RT] ← ¬(RA) + 1
  | .neg rt ra => some (s.setG rt (~~~(s.getG ra) + 1))
  | .cmpldi ra ui =>
    -- a ← GPR[RA]; b ← EXTZ(UI)   (L = 1: 64-bit comparison)
    -- if a <u b then c ← 0b100 else if a >u b then c ← 0b010 else c ← 0b001
    -- CR0 ← c || XER.SO
    let a := s.getG ra
    let b := BitVec.ofNat 64 ui
    some { s with lt := some (BitVec.ult a b), gt := some (BitVec.ult b a), eq := some (a == b) }
  | .adr rt l =>
    match rt with
    | .r0 | .r1 => none
    | _ => some ((s.setG .r0 s.lr).setG rt (s.labels l))

/-- The memory addresses accessed by an instruction. -/
def addrs (i : Instr) (s : State) : List Addr :=
  match i with
  | .lxvw4x _ ra rb | .stxvw4x _ ra rb => [s.ea ra rb]
  | _ => []

/-- `bc 12,2` (branch if `CR0.EQ` = 1) and `bc 4,2` (branch if `CR0.EQ` = 0). -/
def evalCond (c : Cond) (s : State) : Option Bool :=
  match c with
  | .eq => s.eq
  | .ne => s.eq.map (!·)

@[reducible] def isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := evalCond

abbrev Prog := CC.Prog isa

/-! ## The ELFv2 calling convention -/

/-- The nonvolatile GPRs (64-bit ELF V2 ABI §2.2.1.1): `r1` (stack pointer), `r2`
(TOC pointer), `r13` (thread pointer) and `r14`–`r31`. -/
def GReg.nonvolatile : GReg → Bool
  | .r0 | .r3 | .r4 | .r5 | .r6 | .r7 | .r8 | .r9 | .r10 | .r11 | .r12 => false
  | _ => true

/-- The nonvolatile vector registers: `v20`–`v31`. -/
def VReg.nonvolatile : VReg → Bool
  | .v20 | .v21 | .v22 | .v23 | .v24 | .v25 | .v26 | .v27 | .v28 | .v29 | .v30 | .v31 => true
  | _ => false

/-- The registers a function must preserve (ELFv2 §2.2.1.1): the nonvolatile GPRs
and vector registers, the floating-point registers `f14`–`f31` (`VSR[n].dword[0]`),
CR fields 2–4, and the link register (so the function returns to its caller). -/
def CalleeSaved (s s' : State) : Prop :=
  (∀ r : GReg, r.nonvolatile = true → s'.getG r = s.getG r) ∧
  (∀ r : VReg, r.nonvolatile = true → s'.getV r = s.getV r) ∧
  (∀ n : Fin 32, 14 ≤ n.val → dword (s'.vsr n) 0 = dword (s.vsr n) 0) ∧
  s'.cr1to7.extractLsb' 12 12 = s.cr1to7.extractLsb' 12 12 ∧
  s'.lr = s.lr

end CC.Ppc
