import ClaudeCrypto.Ppc.Basic

/-!
Checks the ppc64le model's instruction semantics against test vectors produced
on real hardware / QEMU by `test/ppc_insn_test.c`:

    lake env lean --run ../test/PpcInsnCheck.lean vectors.txt

Every vector is run through `CC.Ppc.exec` itself (so operand order is tested too).
-/

open CC CC.Ppc

def hexVal (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 +
    (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0

/-- The bytes of a hex string, in order. -/
def hexBytes (s : String) : List (BitVec 8) :=
  ((s.toList.toChunks 2).map fun c => BitVec.ofNat 8 (hexVal (String.ofList c)))

def s0 : State :=
  { g := GRegs.mk 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0,
    v := VRegs.mk 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0,
    vsr := fun _ => 0, lr := 0, lt := none, gt := none, eq := none, cr1to7 := 0,
    mem := fun _ => 0, rd := [], wr := [], labels := fun _ => 0 }

def v (s : String) : BitVec 128 := BitVec.ofNat 128 (hexVal s)

/-- Run `i` on a state with `v0, v1, v2 = a, b, c`. -/
def run (i : Instr) (a b c : BitVec 128) : Option State :=
  exec i (((s0.setV .v0 a).setV .v1 b).setV .v2 c)

def base : Addr := 0x10000

/-- A memory holding `bs` at `base`. -/
def memOf (bs : List (BitVec 8)) : Mem := fun a =>
  let k := (a - base).toNat
  if k < bs.length then bs[k]! else 0

def check (line : String) : Bool :=
  let three (i : Instr) (a b c d : String) : Bool :=
    ((run i (v a) (v b) (v c)).map (·.getV .v3)) == some (v d)
  match line.splitOn " " with
  | ["vadduwm", a, b, c, d] => three (.vadduwm .v3 .v0 .v1) a b c d
  | ["vxor", a, b, c, d] => three (.vxor .v3 .v0 .v1) a b c d
  | ["vor", a, b, c, d] => three (.vor .v3 .v0 .v1) a b c d
  | ["vsel", a, b, c, d] => three (.vsel .v3 .v0 .v1 .v2) a b c d
  | ["vperm", a, b, c, d] => three (.vperm .v3 .v0 .v1 .v2) a b c d
  | ["vmrghw", a, b, c, d] => three (.vmrghw .v3 .v0 .v1) a b c d
  | ["vsldoi", sh, a, b, c, d] => three (.vsldoi .v3 .v0 .v1 sh.toNat!) a b c d
  | ["xxpermdi", dm, a, b, c, d] => three (.xxpermdi .v3 .v0 .v1 dm.toNat!) a b c d
  | ["vshasigmaw", st, six, a, b, c, d] =>
    three (.vshasigmaw .v3 .v0 (st == "1") six.toNat!) a b c d
  | ["lxvw4x", bytes, d] =>
    -- EA = (RA|0) + (RB) with RA = 0, RB = r5
    let s := { (s0.setG .r5 base) with mem := memOf (hexBytes bytes), rd := [⟨base, 16⟩] }
    ((exec (.lxvw4x .v3 .r0 .r5) s).map (·.getV .v3)) == some (v d)
  | ["stxvw4x", a, bytes] =>
    -- EA = (RA|0) + (RB) with RA = r4 = base - 7, RB = r5 = 7
    let s := { ((s0.setV .v0 (v a)).setG .r4 (base - 7)).setG .r5 7 with wr := [⟨base, 16⟩] }
    match exec (.stxvw4x .v0 .r4 .r5) s with
    | some s' => (List.range 16).map (fun i => s'.mem (base + BitVec.ofNat 64 i)) == hexBytes bytes
    | none => false
  | ["cmpldi", ui, x, cr] =>
    match exec (.cmpldi .r7 ui.toNat!) (s0.setG .r7 (BitVec.ofNat 64 (hexVal x))) with
    | some s =>
      let c := cr.toNat!
      s.lt == some (c.testBit 2) && s.gt == some (c.testBit 1) && s.eq == some (c.testBit 0)
    | none => false
  | ["addi", x, r1, r2] =>
    let s := s0.setG .r9 (BitVec.ofNat 64 (hexVal x))
    ((exec (.addi .r3 .r9 (-1024)) s).map (·.getG .r3)) == some (BitVec.ofNat 64 (hexVal r1)) &&
    ((exec (.addi .r3 .r9 32767) s).map (·.getG .r3)) == some (BitVec.ofNat 64 (hexVal r2)) &&
    -- `li`: RA = 0 means the value 0
    ((exec (.addi .r3 .r0 (-1024)) s).map (·.getG .r3)) == some (BitVec.ofInt 64 (-1024))
  | ["neg", x, r] =>
    ((exec (.neg .r3 .r9) (s0.setG .r9 (BitVec.ofNat 64 (hexVal x)))).map (·.getG .r3)) ==
      some (BitVec.ofNat 64 (hexVal r))
  | _ => false

def main (args : List String) : IO UInt32 := do
  let lines := (← IO.FS.lines (args.headD "vectors.txt")).toList.filter (· ≠ "")
  let bad := lines.filter (fun l => !check l)
  for l in bad.take 10 do IO.println s!"MISMATCH: {l}"
  IO.println s!"{lines.length - bad.length}/{lines.length} instruction test vectors agree with the model"
  return (if bad.isEmpty && lines.length > 0 then 0 else 1)
