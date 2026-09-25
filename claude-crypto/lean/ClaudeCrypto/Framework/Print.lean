import ClaudeCrypto.Framework.Code

/-!
# Printing structured code as assembly

Structured control flow is lowered to local labels and conditional branches:

* `ite c t e`  ⟶  `b<c> Lthen; e; b Lend; Lthen: t; Lend:`
* `loop body c` ⟶  `Ltop: body; b<c> Ltop`

This lowering (together with each ISA's instruction printer) is part of the
trusted base: it is simple enough to check by inspection, and the emitted
assembly is additionally exercised by the test-suite.
-/

namespace CC

structure Printer (M : ISA) where
  /-- Assembly text for one instruction (may be several lines). -/
  instr : M.Instr → List String
  /-- Conditional branch to a label. -/
  branch : M.Cond → String → String
  /-- Unconditional branch to a label. -/
  jump : String → String
  /-- Return from the function. -/
  ret : List String
  /-- Directives before the function label. -/
  header : String → List String := fun _ => []
  /-- Directives after the function body. -/
  footer : String → List String := fun _ => []

variable {M : ISA} (P : Printer M)

/-- Lower code to lines of assembly, using labels `.L<pfx>_<n>`; returns the
next unused label number. -/
def Printer.lower (pfx : String) : Code M.Instr M.Cond → Nat → List String × Nat
  | .block is, n => ((is.map P.instr).flatten.map ("\t" ++ ·), n)
  | .seq c₁ c₂, n =>
    let (l₁, n) := lower pfx c₁ n
    let (l₂, n) := lower pfx c₂ n
    (l₁ ++ l₂, n)
  | .ite c t e, n =>
    let lThen := s!".L{pfx}_{n}"
    let lEnd := s!".L{pfx}_{n+1}"
    let (le, n) := lower pfx e (n + 2)
    let (lt, n) := lower pfx t n
    (["\t" ++ P.branch c lThen] ++ le ++ ["\t" ++ P.jump lEnd, lThen ++ ":"] ++ lt ++ [lEnd ++ ":"], n)
  | .loop body c, n =>
    let lTop := s!".L{pfx}_{n}"
    let (lb, n) := lower pfx body (n + 1)
    ([lTop ++ ":"] ++ lb ++ ["\t" ++ P.branch c lTop], n)

/-- A complete global function. -/
def Printer.function (name : String) (body : Code M.Instr M.Cond) : String :=
  let (lines, _) := P.lower name body 0
  String.intercalate "\n"
    (P.header name ++ [s!"\t.globl {name}", s!"{name}:"] ++ lines ++ P.ret.map ("\t" ++ ·) ++
      P.footer name) ++ "\n"

end CC
