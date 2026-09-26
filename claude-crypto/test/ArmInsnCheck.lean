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
  | _ => false

def main (args : List String) : IO UInt32 := do
  let lines := (← IO.FS.lines (args.headD "vectors.txt")).toList.filter (· ≠ "")
  let bad := lines.filter (fun l => !check l)
  for l in bad.take 10 do IO.println s!"MISMATCH: {l}"
  IO.println s!"{lines.length - bad.length}/{lines.length} instruction test vectors agree with the model"
  return (if bad.isEmpty && lines.length > 0 then 0 else 1)
