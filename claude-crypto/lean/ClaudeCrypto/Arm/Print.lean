import ClaudeCrypto.Arm.Basic
import ClaudeCrypto.Framework.Print

/-! # GNU as printer for the AArch64 model -/

namespace CC.Arm

def XReg.name (r : XReg) : String := "x" ++ toString r.ctorIdx
def VReg.idx (r : VReg) : Nat := r.ctorIdx

def Arr.name : Arr → String
  | .b16 => "16b"
  | .s4 => "4s"

/-- `v<i>.<arr>` -/
def VReg.arr (r : VReg) (a : String) : String := s!"v{r.idx}.{a}"

def regList (ts : List VReg) (a : Arr) : String :=
  "{" ++ ", ".intercalate (ts.map (·.arr a.name)) ++ "}"

/-- The condition-code suffix of a flag condition (compare-and-branch has none;
`csetm` with one faults in the model, see `condHolds`). -/
def Cond.code : Cond → String
  | .eq => "eq"
  | .ne => "ne"
  | .hs => "hs"
  | .lo => "lo"
  | .hi => "hi"
  | .ls => "ls"
  | .cbz _ | .cbnz _ => "<invalid>"

def Instr.asm : Instr → List String
  | .ldrq t n off => [s!"ldr q{t.idx}, [{n.name}, #{off}]"]
  | .strq t n off => [s!"str q{t.idx}, [{n.name}, #{off}]"]
  | .ld1 ts a n post =>
    [s!"ld1 {regList ts a}, [{n.name}]" ++ (if post then s!", #{16 * ts.length}" else "")]
  | .st1 ts a n post =>
    [s!"st1 {regList ts a}, [{n.name}]" ++ (if post then s!", #{16 * ts.length}" else "")]
  | .rev32 d n => [s!"rev32 {d.arr "16b"}, {n.arr "16b"}"]
  | .addv d n m => [s!"add {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"]
  | .movv d n => [s!"mov {d.arr "16b"}, {n.arr "16b"}"]
  | .sha256h d n m => [s!"sha256h q{d.idx}, q{n.idx}, {m.arr "4s"}"]
  | .sha256h2 d n m => [s!"sha256h2 q{d.idx}, q{n.idx}, {m.arr "4s"}"]
  | .sha256su0 d n => [s!"sha256su0 {d.arr "4s"}, {n.arr "4s"}"]
  | .sha256su1 d n m => [s!"sha256su1 {d.arr "4s"}, {n.arr "4s"}, {m.arr "4s"}"]
  | .adr d l => [s!"adr {d.name}, {l}"]
  | .addi d n imm => [s!"add {d.name}, {n.name}, #{imm}"]
  | .subi d n imm => [s!"sub {d.name}, {n.name}, #{imm}"]
  | .subsi d n imm => [s!"subs {d.name}, {n.name}, #{imm}"]
  | .mov d n => [s!"mov {d.name}, {n.name}"]
  | .addr d n m => [s!"add {d.name}, {n.name}, {m.name}"]
  | .subr d n m => [s!"sub {d.name}, {n.name}, {m.name}"]
  | .adds d n m => [s!"adds {d.name}, {n.name}, {m.name}"]
  | .adcs d n m => [s!"adcs {d.name}, {n.name}, {m.name}"]
  | .subs d n m => [s!"subs {d.name}, {n.name}, {m.name}"]
  | .sbcs d n m => [s!"sbcs {d.name}, {n.name}, {m.name}"]
  | .mul d n m => [s!"mul {d.name}, {n.name}, {m.name}"]
  | .umulh d n m => [s!"umulh {d.name}, {n.name}, {m.name}"]
  | .and d n m => [s!"and {d.name}, {n.name}, {m.name}"]
  | .orr d n m => [s!"orr {d.name}, {n.name}, {m.name}"]
  | .eor d n m => [s!"eor {d.name}, {n.name}, {m.name}"]
  | .lsl d n sh => [s!"lsl {d.name}, {n.name}, #{sh}"]
  | .lsr d n sh => [s!"lsr {d.name}, {n.name}, #{sh}"]
  | .rev d n => [s!"rev {d.name}, {n.name}"]
  | .movz d imm hw => [s!"movz {d.name}, #{imm.toNat}, lsl #{16 * hw}"]
  | .movk d imm hw => [s!"movk {d.name}, #{imm.toNat}, lsl #{16 * hw}"]
  | .csetm d c => [s!"csetm {d.name}, {c.code}"]
  | .ldr t n off => [s!"ldr {t.name}, [{n.name}, #{off}]"]
  | .ldrr t n m => [s!"ldr {t.name}, [{n.name}, {m.name}]"]
  | .str t n off => [s!"str {t.name}, [{n.name}, #{off}]"]
  | .strr t n m => [s!"str {t.name}, [{n.name}, {m.name}]"]
  | .subsp imm => [s!"sub sp, sp, #{imm}"]
  | .addsp imm => [s!"add sp, sp, #{imm}"]
  | .movsp d => [s!"mov {d.name}, sp"]

def Cond.branch (c : Cond) (l : String) : String :=
  match c with
  | .cbz t => s!"cbz {t.name}, {l}"
  | .cbnz t => s!"cbnz {t.name}, {l}"
  | _ => s!"b.{c.code} {l}"

/-- `data` is emitted after the function (in `.text`, so that `adr` reaches it). -/
def printer (data : List String := []) : Printer isa where
  instr := Instr.asm
  branch := Cond.branch
  jump l := s!"b {l}"
  ret := ["ret"]
  header name := ["\t.text", "\t.arch armv8-a+crypto", "\t.p2align 6", s!"\t.type {name}, %function"]
  footer name := [s!"\t.size {name}, .-{name}"] ++ data

end CC.Arm
