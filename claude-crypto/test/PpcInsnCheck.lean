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
    vsr := fun _ => 0, lr := 0, lt := none, gt := none, eq := none, cr1to7 := 0, ca := none,
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

def w64 (s : String) : BitVec 64 := BitVec.ofNat 64 (hexVal s)

/-- `r3 := a op b` via `op r3,r4,r5`. -/
def rrr (i : Instr) (a b r : String) : Bool :=
  ((exec i ((s0.setG .r4 (w64 a)).setG .r5 (w64 b))).map (·.getG .r3)) == some (w64 r)

/-- Carrying instructions: result and `CA`. -/
def rrc (i : Instr) (a b cin r cout : String) : Bool :=
  match exec i { ((s0.setG .r4 (w64 a)).setG .r5 (w64 b)) with ca := some (cin == "1") } with
  | some s => s.getG .r3 == w64 r && s.ca == some (cout == "1")
  | none => false

/-- A state with 32 bytes at `base`, readable and writable, and `r4 = base + o`, `r5 = x`. -/
def memSt (bytes : String) (o x : Nat) : State :=
  { ((s0.setG .r4 (base + BitVec.ofNat 64 o)).setG .r5 (BitVec.ofNat 64 x)) with
    mem := memOf (hexBytes bytes), wr := [⟨base, 32⟩] }

def bytesAt (s : State) : List (BitVec 8) := (List.range 32).map fun i => s.mem (base + BitVec.ofNat 64 i)

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
  | [op, a, b, r] =>
    match op with
    | "add" => rrr (.add .r3 .r4 .r5) a b r
    | "subf" => rrr (.subf .r3 .r4 .r5) a b r
    | "mulld" => rrr (.mulld .r3 .r4 .r5) a b r
    | "mulhdu" => rrr (.mulhdu .r3 .r4 .r5) a b r
    | "and" => rrr (.and .r3 .r4 .r5) a b r
    | "or" => rrr (.or .r3 .r4 .r5) a b r
    | "xor" => rrr (.xor .r3 .r4 .r5) a b r
    | "ori" => ((exec (.ori .r3 .r4 a.toNat!) (s0.setG .r4 (w64 b))).map (·.getG .r3)) == some (w64 r)
    | "oris" => ((exec (.oris .r3 .r4 a.toNat!) (s0.setG .r4 (w64 b))).map (·.getG .r3)) == some (w64 r)
    | "ldx" | "ldbrx" =>
      -- `ldx r3,r4,r5` with r4 = base, r5 = index
      let i : Instr := if op == "ldx" then .ldx .r3 .r4 .r5 else .ldbrx .r3 .r4 .r5
      ((exec i (memSt b 0 a.toNat!)).map (·.getG .r3)) == some (w64 r)
    | "stdx" =>
      -- `stdx r6,r4,r5` with r4 = base, r5 = index, into a zeroed buffer
      match exec (.stdx .r6 .r4 .r5) ((memSt (String.ofList (List.replicate 64 '0')) 0 a.toNat!).setG .r6 (w64 b)) with
      | some s => bytesAt s == hexBytes r
      | none => false
    | _ => false
  | ["stdu", o, ds, a, pa, r] =>
    -- `stdu r6,ds(r4)` with r4 = base + o, into a zeroed buffer; r4 is updated
    let dsI : Int := if ds.startsWith "-" then -((ds.drop 1).toString.toNat! : Int) else ds.toNat!
    let st : State := { ((memSt (String.ofList (List.replicate 96 '0')) o.toNat! 0).setG .r6 (w64 a)) with
      wr := [⟨base, 48⟩] }
    match exec (.stdu .r6 .r4 dsI) st with
    | some s => (List.range 48).map (fun i => s.mem (base + BitVec.ofNat 64 i)) == hexBytes r &&
        s.getG .r4 == base + BitVec.ofNat 64 pa.toNat!
    | none => false
  | [op, a, b, cin, r, cout] =>
    match op with
    | "addc" => rrc (.addc .r3 .r4 .r5) a b cin r cout
    | "adde" => rrc (.adde .r3 .r4 .r5) a b cin r cout
    | "subfc" => rrc (.subfc .r3 .r4 .r5) a b cin r cout
    | "subfe" => rrc (.subfe .r3 .r4 .r5) a b cin r cout
    | _ => false
  | [op, x, y, a, r] =>
    match op with
    | "rldicl" => ((exec (.rldicl .r3 .r4 x.toNat! y.toNat!) (s0.setG .r4 (w64 a))).map (·.getG .r3)) == some (w64 r)
    | "rldicr" => ((exec (.rldicr .r3 .r4 x.toNat! y.toNat!) (s0.setG .r4 (w64 a))).map (·.getG .r3)) == some (w64 r)
    | "ld" =>
      -- `ld r3,ds(r4)` with r4 = base + o
      ((exec (.ld .r3 .r4 y.toNat!) (memSt a x.toNat! 0)).map (·.getG .r3)) == some (w64 r)
    | "std" =>
      -- `std r6,ds(r4)` with r4 = base + o, into a zeroed buffer
      match exec (.std .r6 .r4 y.toNat!) ((memSt (String.ofList (List.replicate 64 '0')) x.toNat! 0).setG .r6 (w64 a)) with
      | some s => bytesAt s == hexBytes r
      | none => false
    | _ => false
  | _ => false

def main (args : List String) : IO UInt32 := do
  let lines := (← IO.FS.lines (args.headD "vectors.txt")).toList.filter (· ≠ "")
  let bad := lines.filter (fun l => !check l)
  for l in bad.take 10 do IO.println s!"MISMATCH: {l}"
  IO.println s!"{lines.length - bad.length}/{lines.length} instruction test vectors agree with the model"
  return (if bad.isEmpty && lines.length > 0 then 0 else 1)
