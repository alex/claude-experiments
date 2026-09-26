import ClaudeCrypto.X86.Print

/-!
Checks the x86-64 model's instruction semantics (`CC.X86.exec`, `CC.X86.evalCond`)
against test vectors produced on real hardware by `test/x86_insn_test.c`:

    lake env lean --run ../test/X86InsnCheck.lean vectors.txt

## Design

The list of instruction forms tested is `forms` below: `Instr` values (plus one
conditional branch per `Cond`).  `--gen` prints that list as the C form table of
`x86_insn_test.c` (between its `BEGIN/END GENERATED FORMS` markers), with the
assembly text of each form produced by the model's own printer
(`CC.X86.Instr.asm`); the C harness assembles exactly that text.

The C harness loads *all* 16 general-purpose registers, RFLAGS, all 16 ymm
registers (for vector forms) and a 128-byte memory buffer with random values,
executes the instruction, and prints the complete input state and the
complete output state (as a diff).  For every vector this checker

* looks the form up by its assembly text (so the C side and the model agree on
  which `Instr` was executed, and the printer is tested too);
* builds the same input state, runs `exec` (or `evalCond` for a branch);
* requires the model not to fault, and compares all 16 GPRs, all 16 ymm
  registers, the memory buffer, and each of CF/ZF/SF/OF that the model
  defines (a flag the model leaves undefined, `none`, is not compared).

Finally it checks coverage: every constructor of `Instr` and `Cond`, both
operand sizes, every ALU op × size × source kind, every shift op × size and every
addressing mode has at least `minVectors` vectors (instructions needing a CPU
feature the machine lacks are reported instead, when the harness says so).
-/

open CC CC.X86

/-! ## Instruction forms -/

inductive Form
  | ins (i : Instr)
  /-- `j<c> 1f; mov rax, 0; jmp 2f; 1: mov rax, 1; 2:` -/
  | jcc (c : Cond)

instance : Inhabited Form := ⟨.jcc .e⟩
instance : Inhabited MemOp := ⟨{}⟩

def Form.text : Form → String
  | .ins i => "; ".intercalate i.asm
  | .jcc c => printer.branch c "1f" ++ "; mov rax, 0; jmp 2f; 1: mov rax, 1; 2:"

def gprs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- Register pairs (dst, src) of different parity: the edge-case vectors of the
harness give even and odd registers independent edge values. -/
def pairs : List (Reg × Reg) :=
  [(.rax, .rcx), (.rbx, .rdx), (.rsi, .r15), (.r8, .rbp), (.r13, .r10), (.rdi, .r12),
   (.r11, .r14), (.r9, .rax), (.rdx, .r13), (.r14, .rbx), (.rcx, .r8), (.r15, .r12)]

def vregs : List VReg :=
  [.y0, .y1, .y2, .y3, .y4, .y5, .y6, .y7, .y8, .y9, .y10, .y11, .y12, .y13, .y14, .y15]

def pick {α : Type} [Inhabited α] (l : List α) (k : Nat) : α := l[k % l.length]!

/-- The label the harness places its memory buffer at. -/
def bufLabel : String := "g_buf"

/-- Addressing modes: every base register kind (incl. `rsp`, `rbp`, `r12`, `r13`,
which need special encodings), all scales, 8- and 32-bit and negative
displacements, and RIP-relative. -/
def memOps : List MemOp :=
  [{ base := .rdi },
   { base := .rsi, disp := 8 },
   { base := .rsp, disp := 24 },
   { rip := some bufLabel, disp := 3 },
   { base := .rbp, disp := -16 },
   { base := .r13 },
   { base := .rdx, index := some .rcx },
   { base := .r12, disp := 40 },
   { base := .rbx, index := some .r9, scale := 2, disp := 7 },
   { base := .r10, index := some .rbp, scale := 4, disp := -100 },
   { rip := some bufLabel },
   { base := .r15, index := some .r11, scale := 8, disp := 0x12345 },
   { base := .rax, index := some .rdx, scale := 8, disp := -0x7ffff000 },
   { base := .r8, index := some .rsi, scale := 1, disp := 127 },
   { base := .rsp, index := some .r14, scale := 4, disp := -128 },
   { rip := some bufLabel, disp := 61 }]

def imms : List Int :=
  [0, 1, -1, 0x7f, -0x80, 0x80, 0x7fffffff, -0x80000000, 0x12345678, -0x3c5a9687, 1249150122,
   -1538233109, 0xff, 0xffff, 64, -32]

def imm (k : Nat) : BitVec 32 := BitVec.ofInt 32 (pick imms k)

def aluOps : List AluOp := [.add, .adc, .sub, .sbb, .and, .or, .xor, .cmp, .test]
def shiftOps : List ShiftOp := [.ror, .rol, .shr, .shl]
def conds : List Cond := [.e, .ne, .b, .ae, .be, .a]

/-- Shift/rotate counts: 0, 1, the masking boundaries and beyond. -/
def shiftCounts : Sz → List Nat
  | .d => [0, 1, 2, 7, 16, 31, 32, 33, 63, 255]
  | .q => [0, 1, 2, 7, 31, 32, 33, 63, 64, 65, 127, 255]

def rorxCounts : Sz → List Nat
  | .d => [0, 1, 6, 13, 31, 32, 255]
  | .q => [0, 1, 6, 28, 32, 41, 63, 64, 255]

def forms : Array Form := Id.run do
  let mut fs : Array Form := #[]
  let mut k := 0
  for sz in [Sz.d, Sz.q] do
    k := k + 1
    -- mov
    for j in [0, 5, 9] do
      let p := pick pairs (j + k)
      fs := fs.push (.ins (.mov sz p.1 (.reg p.2)))
    fs := fs.push (.ins (.mov sz .rbx (.reg .rbx)))
    for j in [0:6] do
      fs := fs.push (.ins (.mov sz (pick gprs (j + k)) (.imm (imm (3 * j + k)))))
    for (m, j) in memOps.zipIdx do
      fs := fs.push (.ins (.mov sz (pick gprs (j + 3 * k)) (.mem m)))
    -- store
    for (m, j) in memOps.zipIdx do
      fs := fs.push (.ins (.store sz m (pick gprs (2 * j + k))))
    -- two-operand ALU
    for (op, oi) in aluOps.zipIdx do
      let n := 2 * oi + k
      let p := pick pairs n
      fs := fs.push (.ins (.alu op sz p.1 (.reg p.2)))
      fs := fs.push (.ins (.alu op sz (pick gprs (n + 4)) (.reg (pick gprs (n + 4)))))
      for j in [0:3] do
        fs := fs.push (.ins (.alu op sz (pick gprs (n + j)) (.imm (imm (3 * n + j)))))
      for j in [0, 7] do
        fs := fs.push (.ins (.alu op sz (pick gprs (n + j + 2)) (.mem (pick memOps (n + j)))))
    -- lea
    for (m, j) in memOps.zipIdx do
      fs := fs.push (.ins (.lea sz (pick gprs (j + k)) m))
    -- rorx
    for (n, j) in (rorxCounts sz).zipIdx do
      let p := pick pairs (j + k)
      fs := fs.push (.ins (.rorx sz p.1 p.2 n))
    fs := fs.push (.ins (.rorx sz .r10 .r10 7))
    -- andn (there is no immediate form)
    fs := fs.push (.ins (.andn sz .rax .rbx (.reg .rcx)))
    fs := fs.push (.ins (.andn sz .r10 .r10 (.reg .r11)))
    fs := fs.push (.ins (.andn sz .r12 .r13 (.reg .r12)))
    fs := fs.push (.ins (.andn sz .rsi .rdi (.reg .rdi)))
    fs := fs.push (.ins (.andn sz .r8 .r8 (.reg .r8)))
    for j in [1, 8, 11] do
      fs := fs.push (.ins (.andn sz (pick gprs (j + 1)) (pick gprs (j + 6)) (.mem (pick memOps (j + k)))))
    -- shifts and rotates by an immediate
    for (op, oi) in shiftOps.zipIdx do
      for (n, j) in (shiftCounts sz).zipIdx do
        fs := fs.push (.ins (.shift op sz (pick gprs (oi + 3 * j + k)) n))
    -- unary
    for r in [Reg.rax, .r14] do
      fs := fs.push (.ins (.not sz r))
    for r in [Reg.rcx, .r9, .rbp] do
      fs := fs.push (.ins (.bswap sz r))
    for r in [Reg.rdx, .r11] do
      fs := fs.push (.ins (.inc sz r))
      fs := fs.push (.ins (.dec sz r))
    -- movbe (load form)
    for j in [0, 3, 8, 12, 15] do
      fs := fs.push (.ins (.movbe sz (pick gprs (j + k)) (pick memOps (j + k))))
  -- stack-pointer arithmetic as used by the function prologues
  fs := fs.push (.ins (.alu .sub .q .rsp (.imm 1792)))
  fs := fs.push (.ins (.alu .add .q .rsp (.imm 512)))
  fs := fs.push (.ins (.alu .and .q .rsp (.imm (BitVec.ofInt 32 (-32)))))
  fs := fs.push (.ins (.mov .q .r15 (.reg .rsp)))
  fs := fs.push (.ins (.mov .q .rsp (.reg .rbp)))
  -- push / pop (including rsp itself)
  for r in [Reg.rax, .rbx, .rsp, .rbp, .r12, .r15] do
    fs := fs.push (.ins (.push r))
  for r in [Reg.rcx, .rbp, .rsp, .r13, .rdi] do
    fs := fs.push (.ins (.pop r))
  -- mulx (incl. hi = lo, and rdx / src aliasing)
  for (hi, lo, src) in [(Reg.rax, Reg.rbx, Reg.rcx), (.r8, .r9, .rdx), (.rax, .rax, .rbx),
      (.rdx, .rcx, .rbx), (.rbx, .rdx, .rcx), (.r14, .r15, .r14), (.r10, .r11, .r11)] do
    fs := fs.push (.ins (.mulx hi lo src))
  -- movabs
  for (r, v) in [(Reg.rax, (0 : Int)), (.rbx, -1), (.rbp, 2 ^ 63), (.r15, 0x0123456789abcdef),
      (.r9, 0x80000000), (.rsi, 0xffffffff), (.rdx, 0xfedcba9876543210)] do
    fs := fs.push (.ins (.movabs r (BitVec.ofInt 64 v)))
  -- conditional branches
  for c in conds do
    fs := fs.push (.jcc c)
  -- AVX / AVX2
  let vm (j : Nat) := pick memOps (3 * j + 1)
  for j in [0:5] do
    fs := fs.push (.ins (.vload128 (pick vregs (5 * j + 1)) (vm j)))
    fs := fs.push (.ins (.vload256 (pick vregs (5 * j + 2)) (vm (j + 1))))
    fs := fs.push (.ins (.vstore256 (vm (j + 2)) (pick vregs (5 * j + 3))))
    fs := fs.push (.ins (.vbroadcasti128 (pick vregs (5 * j + 4)) (vm (j + 3))))
    fs := fs.push (.ins (.vpaddd (pick vregs (3 * j)) (pick vregs (3 * j + 7)) (.mem (vm (j + 4)))))
  for (d, s, j) in [(VReg.y0, VReg.y1, 0), (.y9, .y14, 1), (.y5, .y5, 2), (.y15, .y3, 3)] do
    fs := fs.push (.ins (.vinserti128hi d s (vm (j + 5))))
  for (d, a, b) in [(VReg.y0, VReg.y1, VReg.y2), (.y5, .y5, .y12), (.y9, .y3, .y9),
      (.y15, .y8, .y8), (.y7, .y7, .y7), (.y10, .y13, .y4)] do
    fs := fs.push (.ins (.vpshufb d a b))
    fs := fs.push (.ins (.vpaddd d a (.reg b)))
    fs := fs.push (.ins (.vpxor d a b))
  for (n, j) in [0, 1, 4, 8, 12, 15, 16, 17, 24, 31, 32, 255].zipIdx do
    fs := fs.push (.ins (.vpalignr (pick vregs j) (pick vregs (j + 5)) (pick vregs (3 * j + 2)) n))
  for (n, j) in [0, 1, 2, 3, 7, 10, 17, 18, 31, 32, 255].zipIdx do
    fs := fs.push (.ins (.vpsrld (pick vregs (j + 1)) (pick vregs (2 * j)) n))
  for (n, j) in [0, 1, 5, 13, 14, 25, 31, 32, 255].zipIdx do
    fs := fs.push (.ins (.vpslld (pick vregs (j + 3)) (pick vregs (3 * j)) n))
  for (n, j) in [0, 1, 6, 19, 32, 61, 63, 64, 255].zipIdx do
    fs := fs.push (.ins (.vpsrlq (pick vregs (j + 7)) (pick vregs (5 * j)) n))
  for (n, j) in [0x00, 0x1b, 0x4e, 0x93, 0xb1, 0xe4, 0xff, 0x39].zipIdx do
    fs := fs.push (.ins (.vpshufd (pick vregs (j + 2)) (pick vregs (7 * j + 1)) n))
  fs := fs.push (.ins .vzeroupper)
  -- legacy SSE (128-bit, upper ymm bits preserved)
  for j in [0:4] do
    fs := fs.push (.ins (.movdquLd (pick vregs (3 * j + 2)) (vm (j + 6))))
    fs := fs.push (.ins (.movdquSt (vm (j + 7)) (pick vregs (3 * j + 4))))
  for (d, s) in [(VReg.y1, VReg.y2), (.y0, .y11), (.y6, .y6), (.y13, .y4), (.y8, .y15)] do
    fs := fs.push (.ins (.movdqa d s))
    fs := fs.push (.ins (.paddd d s))
    fs := fs.push (.ins (.pshufb d s))
    fs := fs.push (.ins (.punpcklqdq d s))
    fs := fs.push (.ins (.punpckhqdq d s))
    fs := fs.push (.ins (.sha256rnds2 d s))
    fs := fs.push (.ins (.sha256msg1 d s))
    fs := fs.push (.ins (.sha256msg2 d s))
  for (n, j) in [0x00, 0x1b, 0x4e, 0x93, 0xe4, 0xff].zipIdx do
    fs := fs.push (.ins (.pshufd (pick vregs (j + 3)) (pick vregs (5 * j)) n))
  for (n, j) in [0, 1, 4, 8, 12, 15, 16, 17, 31, 32, 255].zipIdx do
    fs := fs.push (.ins (.palignr (pick vregs (j + 1)) (pick vregs (3 * j + 6)) n))
  return fs

/-! ## Form metadata for the C harness -/

def CC.X86.Reg.idx (r : Reg) : Nat := r.ctorIdx

/-- The memory operand of an instruction and the access size in bytes. -/
def memAccess : Instr → Option (MemOp × Nat)
  | .mov sz _ (.mem m) | .alu _ sz _ (.mem m) | .andn sz _ _ (.mem m) | .store sz m _
  | .movbe sz _ m => some (m, sz.bits / 8)
  | .vload128 _ m | .vinserti128hi _ _ m | .vbroadcasti128 _ m | .movdquLd _ m | .movdquSt m _ =>
    some (m, 16)
  | .vload256 _ m | .vstore256 m _ | .vpaddd _ _ (.mem m) => some (m, 32)
  | _ => none

/-- Instructions that read or write vector registers. -/
def isVec : Instr → Bool
  | .vload128 .. | .vload256 .. | .vstore256 .. | .vinserti128hi .. | .vbroadcasti128 ..
  | .vpshufb .. | .vpaddd .. | .vpxor .. | .vpalignr .. | .vpsrld .. | .vpslld .. | .vpsrlq ..
  | .vpshufd .. | .vzeroupper | .movdquLd .. | .movdquSt .. | .movdqa .. | .paddd .. | .pshufb ..
  | .pshufd .. | .palignr .. | .punpcklqdq .. | .punpckhqdq .. | .sha256rnds2 .. | .sha256msg1 ..
  | .sha256msg2 .. => true
  | _ => false

/-- CPU feature needed beyond x86-64 + AVX2/BMI1/BMI2/MOVBE (1 = SHA extensions). -/
def feature : Form → Nat
  | .ins (.sha256rnds2 ..) | .ins (.sha256msg1 ..) | .ins (.sha256msg2 ..) => 1
  | _ => 0

def featureName : Nat → String
  | 1 => "sha"
  | _ => "base"

/-- The (sign-extended) immediate operand of an ALU instruction. -/
def aluImm : Form → Option Int
  | .ins (.alu _ _ _ (.imm v)) => some v.toInt
  | _ => none

/-- `F(id, "text", vec, kind, base, index, scale, disp, size, feature, hasimm, imm)`:
kind 0 = no memory access, 1 = memory operand, 2 = push, 3 = pop;
base/index are register numbers (-1 = none; base -1 with kind 1 = RIP-relative);
`imm` is the ALU immediate (the harness then also tries register values near it). -/
def Form.cEntry (id : Nat) (f : Form) : String :=
  let (vec, kind, base, index, scale, disp, size) : Nat × Nat × Int × Int × Nat × Int × Nat :=
    match f with
    | .jcc _ => (0, 0, -1, -1, 1, 0, 0)
    | .ins i =>
      let vec := if isVec i then 1 else 0
      match i, memAccess i with
      | .push _, _ => (vec, 2, -1, -1, 1, 0, 8)
      | .pop _, _ => (vec, 3, -1, -1, 1, 0, 8)
      | _, some (m, n) =>
        let base : Int := if m.rip.isSome then -1 else m.base.idx
        let index : Int := if m.rip.isSome then -1 else (m.index.map (Int.ofNat ·.idx)).getD (-1)
        (vec, 1, base, index, m.scale, m.disp, n)
      | _, none => (vec, 0, -1, -1, 1, 0, 0)
  let (hasImm, imm) := match aluImm f with | some v => (1, v) | none => (0, 0)
  s!"  F({id}, \"{f.text}\", {vec}, {kind}, {base}, {index}, {scale}, {disp}LL, {size}, {feature f}, {hasImm}, {imm}LL)"

/-! ## Coverage keys -/

open Lean Elab Term Meta in
/-- The constructor names of an inductive type. -/
elab "ctor_names% " id:ident : term => do
  let n ← realizeGlobalConstNoOverload id
  let some (.inductInfo i) := (← getEnv).find? n | throwError "{n} is not an inductive type"
  return toExpr (i.ctors.map fun c => c.getString!)

def instrCtors : List String := ctor_names% CC.X86.Instr
def condCtors : List String := ctor_names% CC.X86.Cond
def aluCtors : List String := ctor_names% CC.X86.AluOp
def shiftCtors : List String := ctor_names% CC.X86.ShiftOp

def CC.X86.Sz.str : Sz → String | .d => "32" | .q => "64"
def CC.X86.Src.kind : Src → String | .reg _ => "reg" | .imm _ => "imm" | .mem _ => "mem"

def CC.X86.MemOp.mode (m : MemOp) : String :=
  if m.rip.isSome then "rip" else
  match m.index with
  | none => if m.disp = 0 then "base" else "base+disp"
  | some _ => s!"base+index*{m.scale}"

/-- The features of the model a form exercises. -/
def Form.keys : Form → List String
  | .jcc c => [s!"jcc/{condCtors[c.ctorIdx]!}"]
  | .ins i =>
    let c := instrCtors[i.ctorIdx]!
    let sized : List String := match i with
      | .mov sz .. | .store sz .. | .alu _ sz .. | .lea sz .. | .rorx sz .. | .andn sz ..
      | .shift _ sz .. | .not sz .. | .movbe sz .. | .bswap sz .. | .inc sz .. | .dec sz .. =>
        [s!"{c}/{sz.str}"]
      | _ => []
    let sub : List String := match i with
      | .mov sz _ src => [s!"mov/{sz.str}/{src.kind}"]
      | .andn sz _ _ src => [s!"andn/{sz.str}/{src.kind}"]
      | .alu op sz _ src => [s!"alu/{aluCtors[op.ctorIdx]!}/{sz.str}/{src.kind}"]
      | .shift op sz .. => [s!"shift/{shiftCtors[op.ctorIdx]!}/{sz.str}"]
      | .vpaddd _ _ (.reg _) => ["vpaddd/reg"]
      | .vpaddd _ _ (.mem _) => ["vpaddd/mem"]
      | _ => []
    let mode : List String := match i with
      | .lea _ _ m => [s!"mode/{m.mode}"]
      | _ => match memAccess i with
        | some (m, _) => [s!"mode/{m.mode}"]
        | none => []
    [c] ++ sized ++ sub ++ mode

def requiredKeys : List String :=
  let szs := ["32", "64"]
  instrCtors ++ condCtors.map (s!"jcc/{·}") ++
  (["mov", "store", "alu", "lea", "rorx", "andn", "shift", "not", "movbe", "bswap", "inc", "dec"].flatMap
    fun c => szs.map (s!"{c}/{·}")) ++
  (szs.flatMap fun sz => ["reg", "imm", "mem"].map (s!"mov/{sz}/{·}")) ++
  (szs.flatMap fun sz => ["reg", "mem"].map (s!"andn/{sz}/{·}")) ++
  (aluCtors.flatMap fun op => szs.flatMap fun sz => ["reg", "imm", "mem"].map (s!"alu/{op}/{sz}/{·}")) ++
  (shiftCtors.flatMap fun op => szs.map (s!"shift/{op}/{·}")) ++
  ["vpaddd/reg", "vpaddd/mem"] ++
  ["base", "base+disp", "base+index*1", "base+index*2", "base+index*4", "base+index*8", "rip"].map
    (s!"mode/{·}")

/-! ## Running a vector -/

def hex? (s : String) : Option Nat := Lean.Syntax.decodeNatLitVal? ("0x" ++ s)

def hexStr (n : Nat) (digits : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (digits - s.length) '0') ++ s

def allRegs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

def zeroRegs : Regs := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def zeroVRegs : VRegs := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- RFLAGS bits. -/
def cfBit := 0
def zfBit := 6
def sfBit := 7
def ofBit := 11

/-- Parse `k=hex,k=hex,…` (or `-`) into a list of (index, value). -/
def parseDiff (s : String) : Option (List (Nat × Nat)) :=
  if s == "-" then some [] else
  (s.splitOn ",").mapM fun kv =>
    match kv.splitOn "=" with
    | [k, v] => do pure (← k.toNat?, ← hex? v)
    | _ => none

/-- Parse `n` comma-separated hex words. -/
def parseWords (s : String) (n : Nat) : Option (List Nat) := do
  let ws ← (s.splitOn ",").mapM hex?
  if ws.length == n then some ws else none

structure Env where
  bufAddr : Addr
  bufLen : Nat

/-- The `n` bytes of the little-endian number `x`. -/
def bytesOf (x n : Nat) : Array (BitVec 8) := Id.run do
  let mut a := Array.emptyWithCapacity n
  let mut x := x
  for _ in [0:n] do
    a := a.push (BitVec.ofNat 8 x)
    x := x / 256
  return a

/-- Memory holding `bytes` at the buffer address (and zero elsewhere). -/
def memOf (env : Env) (bytes : Array (BitVec 8)) : Mem := fun a =>
  let k := (a - env.bufAddr).toNat
  if h : k < bytes.size then bytes[k] else 0

/-- Instructions that write memory; the others get the buffer as a read-only
region, so a spurious write by the model makes it fault. -/
def writesMem : Form → Bool
  | .ins (.store ..) | .ins (.push _) | .ins (.vstore256 ..) | .ins (.movdquSt ..) => true
  | _ => false

def runForm : Form → State → Option State
  | .ins i, s => exec i s
  | .jcc c, s => (evalCond c s).map fun b => s.setReg .rax (if b then 1 else 0)

/-- Check one vector line (already split into fields); `none` if it agrees,
otherwise a description of the discrepancy. -/
def checkVector (env : Env) (f : Form) (fin gin vin buf fout gout vout bufout : String) :
    Option String := Id.run do
  let parsed : Option _ := do
    let fin ← hex? fin
    let gin ← parseWords gin 16
    let vin ← if vin == "-" then pure (List.replicate 16 0) else parseWords vin 16
    let buf ← if buf == "-" then pure none else (hex? buf).map some
    let fout ← hex? fout
    let gout ← parseDiff gout
    let vout ← parseDiff vout
    let bufout ← if bufout == "-" then pure none else (hex? bufout).map some
    pure (fin, gin, vin, buf, fout, gout, vout, bufout)
  let some (fin, gin, vin, buf, fout, gout, vout, bufout) := parsed | return some "unparsable vector"
  let regs := (allRegs.zip gin).foldl (fun g (r, v) => g.set r (BitVec.ofNat 64 v)) zeroRegs
  let vecs := (vregs.zip vin).foldl (fun g (r, v) => g.set r (BitVec.ofNat 256 v)) zeroVRegs
  let region : List Region := if buf.isSome then [⟨env.bufAddr, env.bufLen⟩] else []
  let bufBytes := bytesOf (buf.getD 0) env.bufLen
  let s : State :=
    { gpr := regs, vec := vecs,
      cf := some (fin.testBit cfBit), zf := some (fin.testBit zfBit),
      sf := some (fin.testBit sfBit), of := some (fin.testBit ofBit),
      mem := memOf env bufBytes, labels := fun _ => env.bufAddr,
      rd := if writesMem f then [] else region, wr := if writesMem f then region else [] }
  let some s' := runForm f s | return some "the model faults"
  let mut errs : Array String := #[]
  for (r, i) in allRegs.zipIdx do
    let hw := ((gout.lookup i).getD gin[i]!)
    if (s'.gpr.get r).toNat != hw then
      errs := errs.push s!"{r.name64}: model {hexStr (s'.gpr.get r).toNat 16} cpu {hexStr hw 16}"
  for (v, i) in vregs.zipIdx do
    let hw := ((vout.lookup i).getD vin[i]!)
    if (s'.vec.get v).toNat != hw then
      errs := errs.push s!"{v.name}: model {hexStr (s'.vec.get v).toNat 64} cpu {hexStr hw 64}"
  for (name, bit, m) in [("CF", cfBit, s'.cf), ("ZF", zfBit, s'.zf), ("SF", sfBit, s'.sf),
      ("OF", ofBit, s'.of)] do
    if let some b := m then
      if b != fout.testBit bit then errs := errs.push s!"{name}: model {b} cpu {fout.testBit bit}"
  if buf.isSome && writesMem f then
    let hw := bytesOf (bufout.getD 0) env.bufLen
    for k in [0:env.bufLen] do
      let m := s'.mem (env.bufAddr + BitVec.ofNat 64 k)
      if m != hw[k]! then
        errs := errs.push s!"memory byte {k}: model {hexStr m.toNat 2} cpu {hexStr hw[k]!.toNat 2}"
  else if bufout != buf then
    errs := errs.push "memory: the CPU changed memory, the model cannot (read-only region)"
  return if errs.isEmpty then none else some (", ".intercalate errs.toList)

/-! ## Main -/

def minVectors : Nat := 500

def genC : IO Unit := do
  IO.println "#define FORMS(F) \\"
  for (f, id) in forms.toList.zipIdx do
    IO.println (f.cEntry id ++ " \\")
  IO.println ""

def check (path : String) : IO UInt32 := do
  let byText : Std.HashMap String Nat :=
    forms.toList.zipIdx.foldl (fun m (f, i) => m.insert f.text i) {}
  let h ← IO.FS.Handle.mk path .read
  let mut env : Env := ⟨0, 0⟩
  let mut idMap : Std.HashMap Nat Nat := {}      -- C form id ↦ index into `forms`
  let mut counts : Array Nat := Array.replicate forms.size 0
  let mut failures : Array Nat := Array.replicate forms.size 0
  let mut missingFeatures : List Nat := []
  let mut total := 0
  let mut bad := 0
  let mut errors : Array String := #[]
  let mut unknown : Std.HashMap String Nat := {}  -- vectors of forms not in the model's list
  let mut shown := 0
  repeat
    let line ← h.getLine
    if line.isEmpty then break
    let line := line.trimAscii.toString
    if line.isEmpty then continue
    match line.splitOn " " with
    | ["b", addr, len] =>
      env := ⟨BitVec.ofNat 64 ((hex? addr).getD 0), len.toNat!⟩
    | ["nofeature", n, _] => missingFeatures := n.toNat! :: missingFeatures
    | "f" :: id :: text =>
      let text := " ".intercalate text
      match byText[text]? with
      | some i => idMap := idMap.insert id.toNat! i
      | none => errors := errors.push s!"form {id} `{text}` is not the printer's text of any modelled form"
    | ["v", id, fin, gin, vin, buf, fout, gout, vout, bufout] =>
      total := total + 1
      match idMap[id.toNat!]? with
      | none =>
        bad := bad + 1
        unknown := unknown.insert id (unknown.getD id 0 + 1)
      | some fi =>
        let f := forms[fi]!
        match checkVector env f fin gin vin buf fout gout vout bufout with
        | none => counts := counts.modify fi (· + 1)
        | some e =>
          bad := bad + 1
          failures := failures.modify fi (· + 1)
          if failures[fi]! ≤ 3 && shown < 60 then
            shown := shown + 1
            errors := errors.push s!"MISMATCH `{f.text}`: {e}\n    vector: {line}"
    | _ =>
      bad := bad + 1
      errors := errors.push s!"malformed line: {line.take 80}"
  for e in errors do IO.println e
  for (id, n) in unknown.toList do
    IO.println s!"{n} vectors for form {id}, which is not a modelled form"
  for (f, i) in forms.toList.zipIdx do
    if failures[i]! > 0 then
      IO.println s!"FAILED: `{f.text}`: {failures[i]!} of {failures[i]! + counts[i]!} vectors disagree"
  -- coverage
  let mut keyCount : Std.HashMap String Nat := {}
  let mut skipped : Std.HashMap String Nat := {}
  let mut thin : Array String := #[]
  for (f, i) in forms.toList.zipIdx do
    let n := counts[i]!
    let feat := feature f
    if feat != 0 && missingFeatures.contains feat && n == 0 then
      for key in f.keys do skipped := skipped.insert key feat
    else if n < minVectors && failures[i]! == 0 then
      thin := thin.push s!"`{f.text}` ({n} vectors)"
    for key in f.keys do keyCount := keyCount.modify key (· + n) |>.insertIfNew key n
  let uncovered := requiredKeys.filter fun k => (keyCount.getD k 0) < minVectors && !skipped.contains k
  let untestable := requiredKeys.filter fun k => (keyCount.getD k 0) < minVectors && skipped.contains k
  for t in thin do IO.println s!"TOO FEW VECTORS: {t}"
  for k in uncovered do IO.println s!"NOT COVERED: {k}"
  for k in untestable do
    IO.println s!"not tested: {k} (the CPU lacks the {featureName (skipped.getD k 0)} extension)"
  let tested := forms.toList.zipIdx.filter (fun (_, i) => counts[i]! > 0)
  IO.println s!"{instrCtors.length - (untestable.filter instrCtors.contains).length}/{instrCtors.length} Instr constructors, {condCtors.length} conditions, {tested.length}/{forms.size} forms tested"
  for c in instrCtors do
    IO.println s!"  {c}: {keyCount.getD c 0} vectors"
  IO.println s!"{total - bad}/{total} x86-64 instruction test vectors agree with the model"
  let ok := bad == 0 && errors.isEmpty && total > 0 && thin.isEmpty && uncovered.isEmpty
  return if ok then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--gen"] => genC; return 0
  | [path] => check path
  | _ => IO.println "usage: X86InsnCheck (--gen | vectors.txt)"; return 2
