import ClaudeCrypto.Ppc.Basic
import ClaudeCrypto.Framework.Print

/-!
# GNU as printer for the ppc64le model

Registers are printed as plain numbers (GNU as without `-mregnames`): GPR `rN`
as `N`, vector register `vN` as `N` in VMX instructions and as the VSX
register number `32+N` in VSX instructions (`lxvw4x`, `stxvw4x`,
`xxpermdi`).  In X-form loads and stores an `RA` operand of `0` means the
value 0 (`(RA|0)`), exactly as in the model.

The function is emitted for the ELFv2 ABI (`.abiversion 2`).  It uses neither
the TOC pointer `r2` nor `r12`, so it has a single entry point (no
`.localentry`, i.e. `st_other = 0`: local and global entry points coincide
and `r2` is preserved).

The `adr` pseudo-instruction is printed as the position-independent sequence
(cf. OpenSSL's `LPICmeup`)
```
    mflr 0                      # r0 ← LR
    bcl 20,31,1f                # LR ← address of 1:  (special form, does not
1:  mflr rt                     #   disturb the return-address predictor)
    mtlr 0                      # LR ← r0
    addis rt,rt,(label-1b)@ha
    addi rt,rt,(label-1b)@l     # rt ← 1b + (label - 1b)
```
whose net effect is `r0 ← LR; rt ← label` (for `rt ∉ {r0, r1}`); this
expansion is part of the trusted base.  The data tables are emitted in
`.text` after the function.
-/

namespace CC.Ppc

def GReg.num (r : GReg) : Nat := r.ctorIdx
def VReg.num (r : VReg) : Nat := r.ctorIdx
/-- The VSX register number of a vector register: `VSR[32 + n]` is `VR[n]`. -/
def VReg.vsx (r : VReg) : Nat := 32 + r.ctorIdx

def Instr.asm : Instr → List String
  | .lxvw4x t ra rb => [s!"lxvw4x {t.vsx},{ra.num},{rb.num}"]
  | .stxvw4x x ra rb => [s!"stxvw4x {x.vsx},{ra.num},{rb.num}"]
  | .vadduwm t a b => [s!"vadduwm {t.num},{a.num},{b.num}"]
  | .vxor t a b => [s!"vxor {t.num},{a.num},{b.num}"]
  | .vor t a b => [s!"vor {t.num},{a.num},{b.num}"]
  | .vsel t a b c => [s!"vsel {t.num},{a.num},{b.num},{c.num}"]
  | .vperm t a b c => [s!"vperm {t.num},{a.num},{b.num},{c.num}"]
  | .vsldoi t a b sh => [s!"vsldoi {t.num},{a.num},{b.num},{sh}"]
  | .vmrghw t a b => [s!"vmrghw {t.num},{a.num},{b.num}"]
  | .xxpermdi t a b dm => [s!"xxpermdi {t.vsx},{a.vsx},{b.vsx},{dm}"]
  | .vshasigmaw t a st six => [s!"vshasigmaw {t.num},{a.num},{if st then 1 else 0},{six}"]
  | .addi rt ra si => [s!"addi {rt.num},{ra.num},{si}"]
  | .neg rt ra => [s!"neg {rt.num},{ra.num}"]
  | .cmpldi ra ui => [s!"cmpli 0,1,{ra.num},{ui}"]
  | .adr rt l =>
    [ "mflr 0",
      "bcl 20,31,1f",
      s!"1:\tmflr {rt.num}",
      "mtlr 0",
      s!"addis {rt.num},{rt.num},({l}-1b)@ha",
      s!"addi {rt.num},{rt.num},({l}-1b)@l" ]

def Cond.branch (c : Cond) (l : String) : String :=
  match c with
  | .eq => s!"bc 12,2,{l}"
  | .ne => s!"bc 4,2,{l}"

/-- `data` is emitted after the function (in `.text`, next to the code that
computes its address). -/
def printer (data : List String := []) : Printer isa where
  instr := Instr.asm
  branch := Cond.branch
  jump l := s!"b {l}"
  ret := ["blr"]
  header name := ["\t.abiversion 2", "\t.machine power8", "\t.text", "\t.p2align 6",
    s!"\t.type {name},@function"]
  footer name := [s!"\t.size {name},.-{name}"] ++ data

end CC.Ppc
