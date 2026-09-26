import ClaudeCrypto.Arm.Basic

/-!
Checks the AArch64 model's instruction semantics against test vectors produced
on real hardware / QEMU by `test/arm_insn_test.c`:

    lake env lean --run ../test/ArmInsnCheck.lean vectors.txt

Every vector is run through `CC.Arm.exec` itself (so operand order is tested too).
-/

open CC CC.Arm

def hexVal (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 +
    (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0

def s0 : State :=
  { x := XRegs.mk 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0, sp := 0, v := VRegs.mk 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0,
    nf := none, zf := none, cf := none, vf := none, mem := fun _ => 0, rd := [], wr := [],
    labels := fun _ => 0 }

def v (s : String) : BitVec 128 := BitVec.ofNat 128 (hexVal s)

/-- Run `i` on a state with `v0, v1, v2 = a, b, c` (and `x1 = x`). -/
def run (i : Instr) (a b c : BitVec 128) (x : BitVec 64 := 0) : Option State :=
  exec i ((((s0.setV .v0 a).setV .v1 b).setV .v2 c).setX .x1 x)

def flagsNibble (s : State) : Option Nat := do
  let n ← s.nf; let z ← s.zf; let c ← s.cf; let vf ← s.vf
  pure (8 * n.toNat + 4 * z.toNat + 2 * c.toNat + vf.toNat)

/-- Decimal, or hexadecimal with a `0x` prefix. -/
def num (s : String) : Nat := if s.startsWith "0x" then hexVal (s.drop 2).toString else s.toNat!

def x64 (s : String) : BitVec 64 := BitVec.ofNat 64 (hexVal s)

/-- The state for a scalar test: `x0 = r0` (`0x5555` unless given), `x1 = x`, `x2 = y`,
flags from the NZCV nibble. -/
def scalarState (x y : String) (nzcv : Nat) (r0 : BitVec 64 := 0x5555) : State :=
  { ((s0.setX .x0 r0).setX .x1 (x64 x)).setX .x2 (x64 y) with
    nf := some (nzcv.testBit 3), zf := some (nzcv.testBit 2), cf := some (nzcv.testBit 1),
    vf := some (nzcv.testBit 0) }

/-- Run a scalar instruction and compare `x0` and the flags. -/
def checkScalar (i : Instr) (x y fi r fo : String) (r0 : BitVec 64 := 0x5555) : Bool :=
  match exec i (scalarState x y fi.toNat! r0) with
  | some s => s.getX .x0 == x64 r && flagsNibble s == some fo.toNat!
  | none => false

def condOf : String → Option Cond
  | "eq" => some .eq | "ne" => some .ne | "hs" => some .hs
  | "lo" => some .lo | "hi" => some .hi | "ls" => some .ls
  | _ => none

/-- The 64-byte test buffer, placed at `bufBase`. -/
def bufBase : Addr := 0x1000
def bufBytes (hex : String) (k : Nat) : Byte :=
  BitVec.ofNat 8 (hexVal ((hex.drop (2 * k)).take 2).toString)
def bufMem (hex : String) : Mem := fun a =>
  let k := (a - bufBase).toNat
  if k < 64 then bufBytes hex k else 0
def bufRegion : Region := ⟨bufBase, 64⟩

/-- The memory after a store agrees with the dump `hex` on the buffer. -/
def memIs (m : Mem) (hex : String) : Bool :=
  (List.range 64).all fun k => m (bufBase + BitVec.ofNat 64 k) == bufBytes hex k

def check (line : String) : Bool :=
  match line.splitOn " " with
  | ["sha256h", a, b, c, d] =>
    ((run (.sha256h .v0 .v1 .v2) (v a) (v b) (v c)).map (·.getV .v0)) == some (v d)
  | ["sha256h2", a, b, c, d] =>
    ((run (.sha256h2 .v0 .v1 .v2) (v a) (v b) (v c)).map (·.getV .v0)) == some (v d)
  | ["sha256su0", a, b, d] =>
    ((run (.sha256su0 .v0 .v1) (v a) (v b) 0).map (·.getV .v0)) == some (v d)
  | ["sha256su1", a, b, c, d] =>
    ((run (.sha256su1 .v0 .v1 .v2) (v a) (v b) (v c)).map (·.getV .v0)) == some (v d)
  | ["rev32", a, d] =>
    ((run (.rev32 .v3 .v0) (v a) 0 0).map (·.getV .v3)) == some (v d)
  | ["addv", a, b, d] =>
    ((run (.addv .v3 .v0 .v1) (v a) (v b) 0).map (·.getV .v3)) == some (v d)
  | ["subs", x, imm, r, f] =>
    match run (.subsi .x0 .x1 imm.toNat!) 0 0 0 (BitVec.ofNat 64 (hexVal x)) with
    | some s => s.getX .x0 == BitVec.ofNat 64 (hexVal r) && flagsNibble s == some f.toNat!
    | none => false
  | ["adds", x, y, fi, r, fo] => checkScalar (.adds .x0 .x1 .x2) x y fi r fo
  | ["adcs", x, y, fi, r, fo] => checkScalar (.adcs .x0 .x1 .x2) x y fi r fo
  | ["subs", x, y, fi, r, fo] => checkScalar (.subs .x0 .x1 .x2) x y fi r fo
  | ["sbcs", x, y, fi, r, fo] => checkScalar (.sbcs .x0 .x1 .x2) x y fi r fo
  | ["addr", x, y, fi, r, fo] => checkScalar (.addr .x0 .x1 .x2) x y fi r fo
  | ["subr", x, y, fi, r, fo] => checkScalar (.subr .x0 .x1 .x2) x y fi r fo
  | ["mul", x, y, fi, r, fo] => checkScalar (.mul .x0 .x1 .x2) x y fi r fo
  | ["umulh", x, y, fi, r, fo] => checkScalar (.umulh .x0 .x1 .x2) x y fi r fo
  | ["and", x, y, fi, r, fo] => checkScalar (.and .x0 .x1 .x2) x y fi r fo
  | ["orr", x, y, fi, r, fo] => checkScalar (.orr .x0 .x1 .x2) x y fi r fo
  | ["eor", x, y, fi, r, fo] => checkScalar (.eor .x0 .x1 .x2) x y fi r fo
  | ["rev", x, y, fi, r, fo] => checkScalar (.rev .x0 .x1) x y fi r fo
  | ["csetm", c, x, y, fi, r, fo] =>
    match condOf c with
    | some c => checkScalar (.csetm .x0 c) x y fi r fo
    | none => false
  | ["lsl", sh, x, y, fi, r, fo] => checkScalar (.lsl .x0 .x1 sh.toNat!) x y fi r fo
  | ["lsr", sh, x, y, fi, r, fo] => checkScalar (.lsr .x0 .x1 sh.toNat!) x y fi r fo
  | ["movz", imm, hw, x, y, fi, r, fo] =>
    checkScalar (.movz .x0 (BitVec.ofNat 16 (num imm)) hw.toNat!) x y fi r fo
  | ["movk", imm, hw, x, y, fi, r, fo] =>
    checkScalar (.movk .x0 (BitVec.ofNat 16 (num imm)) hw.toNat!) x y fi r fo (r0 := x64 x)
  | ["ldr", buf, off, r] =>
    match exec (.ldr .x0 .x1 off.toNat!) ({ s0 with mem := bufMem buf, rd := [bufRegion] }.setX .x1 bufBase) with
    | some s => s.getX .x0 == x64 r
    | none => false
  | ["ldrr", buf, off, r] =>
    match exec (.ldrr .x0 .x1 .x2)
        (({ s0 with mem := bufMem buf, rd := [bufRegion] }.setX .x1 bufBase).setX .x2 (BitVec.ofNat 64 off.toNat!)) with
    | some s => s.getX .x0 == x64 r
    | none => false
  | ["str", buf, off, y, buf2] =>
    match exec (.str .x2 .x1 off.toNat!)
        (({ s0 with mem := bufMem buf, wr := [bufRegion] }.setX .x1 bufBase).setX .x2 (x64 y)) with
    | some s => memIs s.mem buf2
    | none => false
  | ["strr", buf, off, y, buf2] =>
    match exec (.strr .x3 .x1 .x2)
        ((({ s0 with mem := bufMem buf, wr := [bufRegion] }.setX .x1 bufBase).setX .x2
          (BitVec.ofNat 64 off.toNat!)).setX .x3 (x64 y)) with
    | some s => memIs s.mem buf2
    | none => false
  | ["spops", imm, a, b, c] =>
    let st : State := { s0 with sp := x64 a }
    match (exec (.movsp .x0) st).bind (exec (.subsp imm.toNat!)) |>.bind (exec (.movsp .x1))
        |>.bind (exec (.addsp imm.toNat!)) |>.bind (exec (.movsp .x2)) with
    | some s => s.getX .x0 == x64 a && s.getX .x1 == x64 b && s.getX .x2 == x64 c && s.sp == x64 c
    | none => false
  | _ => false

def main (args : List String) : IO UInt32 := do
  let lines := (← IO.FS.lines (args.headD "vectors.txt")).toList.filter (· ≠ "")
  let bad := lines.filter (fun l => !check l)
  for l in bad.take 10 do IO.println s!"MISMATCH: {l}"
  IO.println s!"{lines.length - bad.length}/{lines.length} instruction test vectors agree with the model"
  return (if bad.isEmpty && lines.length > 0 then 0 else 1)
