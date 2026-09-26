import ClaudeCrypto.X86.Basic
import ClaudeCrypto.Framework.Print

/-! # Intel-syntax printer for the x86-64 model (GNU as, `.intel_syntax noprefix`) -/

namespace CC.X86

def Reg.name64 : Reg → String
  | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx"
  | .rsp => "rsp" | .rbp => "rbp" | .rsi => "rsi" | .rdi => "rdi"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

def Reg.name32 : Reg → String
  | .rax => "eax" | .rcx => "ecx" | .rdx => "edx" | .rbx => "ebx"
  | .rsp => "esp" | .rbp => "ebp" | .rsi => "esi" | .rdi => "edi"
  | .r8 => "r8d" | .r9 => "r9d" | .r10 => "r10d" | .r11 => "r11d"
  | .r12 => "r12d" | .r13 => "r13d" | .r14 => "r14d" | .r15 => "r15d"

def Reg.nameSz (r : Reg) : Sz → String
  | .d => r.name32
  | .q => r.name64

def VReg.name (v : VReg) : String := "ymm" ++ toString v.ctorIdx
def VReg.xname (v : VReg) : String := "xmm" ++ toString v.ctorIdx

def MemOp.str (m : MemOp) : String :=
  let d := if m.disp = 0 then "" else if m.disp > 0 then s!"+{m.disp}" else s!"{m.disp}"
  match m.rip with
  | some l => s!"[rip+{l}{d}]"
  | none =>
    let idx := match m.index with
      | none => ""
      | some i => s!"+{i.name64}*{m.scale}"
    s!"[{m.base.name64}{idx}{d}]"

def VSrc.str : VSrc → String
  | .reg v => v.name
  | .mem m => "YMMWORD PTR " ++ m.str

def Sz.ptr : Sz → String
  | .d => "DWORD PTR "
  | .q => "QWORD PTR "

def immStr (v : BitVec 32) : String := toString v.toInt

def Src.str (sz : Sz) : Src → String
  | .reg r => r.nameSz sz
  | .imm v => immStr v
  | .mem m => sz.ptr ++ m.str

def AluOp.name : AluOp → String
  | .add => "add" | .adc => "adc" | .sub => "sub" | .sbb => "sbb" | .and => "and"
  | .or => "or" | .xor => "xor" | .cmp => "cmp" | .test => "test"

def ShiftOp.name : ShiftOp → String
  | .ror => "ror" | .rol => "rol" | .shr => "shr" | .shl => "shl"

def Instr.asm : Instr → List String
  | .mov sz d s => [s!"mov {d.nameSz sz}, {s.str sz}"]
  | .store sz m r => [s!"mov {sz.ptr}{m.str}, {r.nameSz sz}"]
  | .alu op sz d s => [s!"{op.name} {d.nameSz sz}, {s.str sz}"]
  | .lea sz d m => [s!"lea {d.nameSz sz}, {m.str}"]
  | .rorx sz d s n => [s!"rorx {d.nameSz sz}, {s.nameSz sz}, {n}"]
  | .andn sz d s1 s2 => [s!"andn {d.nameSz sz}, {s1.nameSz sz}, {s2.str sz}"]
  | .shift op sz d n => [s!"{op.name} {d.nameSz sz}, {n}"]
  | .not sz d => [s!"not {d.nameSz sz}"]
  | .movbe sz d m => [s!"movbe {d.nameSz sz}, {sz.ptr}{m.str}"]
  | .bswap sz d => [s!"bswap {d.nameSz sz}"]
  | .push r => [s!"push {r.name64}"]
  | .pop r => [s!"pop {r.name64}"]
  | .inc sz d => [s!"inc {d.nameSz sz}"]
  | .dec sz d => [s!"dec {d.nameSz sz}"]
  | .vload128 d m => [s!"vmovdqu {d.xname}, XMMWORD PTR {m.str}"]
  | .vload256 d m => [s!"vmovdqu {d.name}, YMMWORD PTR {m.str}"]
  | .vstore256 m v => [s!"vmovdqu YMMWORD PTR {m.str}, {v.name}"]
  | .vinserti128hi d v m => [s!"vinserti128 {d.name}, {v.name}, XMMWORD PTR {m.str}, 1"]
  | .vbroadcasti128 d m => [s!"vbroadcasti128 {d.name}, XMMWORD PTR {m.str}"]
  | .vpshufb d a c => [s!"vpshufb {d.name}, {a.name}, {c.name}"]
  | .vpaddd d a b => [s!"vpaddd {d.name}, {a.name}, {b.str}"]
  | .vpxor d a b => [s!"vpxor {d.name}, {a.name}, {b.name}"]
  | .vpalignr d a b n => [s!"vpalignr {d.name}, {a.name}, {b.name}, {n}"]
  | .vpsrld d a n => [s!"vpsrld {d.name}, {a.name}, {n}"]
  | .vpslld d a n => [s!"vpslld {d.name}, {a.name}, {n}"]
  | .vpsrlq d a n => [s!"vpsrlq {d.name}, {a.name}, {n}"]
  | .vpshufd d a n => [s!"vpshufd {d.name}, {a.name}, {n}"]
  | .vzeroupper => ["vzeroupper"]

def Cond.name : Cond → String
  | .e => "e" | .ne => "ne" | .b => "b" | .ae => "ae" | .be => "be" | .a => "a"

def printer : Printer isa where
  instr := Instr.asm
  branch c l := s!"j{c.name} {l}"
  jump l := s!"jmp {l}"
  ret := ["ret"]
  header name := ["\t.text", "\t.intel_syntax noprefix", "\t.p2align 5", s!"\t.type {name}, @function"]
  footer name := [s!"\t.size {name}, .-{name}", "\t.att_syntax prefix"]

end CC.X86
