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

def Cond.branch (c : Cond) (l : String) : String :=
  match c with
  | .eq => s!"b.eq {l}"
  | .ne => s!"b.ne {l}"
  | .hs => s!"b.hs {l}"
  | .lo => s!"b.lo {l}"
  | .hi => s!"b.hi {l}"
  | .ls => s!"b.ls {l}"
  | .cbz t => s!"cbz {t.name}, {l}"
  | .cbnz t => s!"cbnz {t.name}, {l}"

/-- `data` is emitted after the function (in `.text`, so that `adr` reaches it). -/
def printer (data : List String := []) : Printer isa where
  instr := Instr.asm
  branch := Cond.branch
  jump l := s!"b {l}"
  ret := ["ret"]
  header name := ["\t.text", "\t.arch armv8-a+crypto", "\t.p2align 6", s!"\t.type {name}, %function"]
  footer name := [s!"\t.size {name}, .-{name}"] ++ data

end CC.Arm
