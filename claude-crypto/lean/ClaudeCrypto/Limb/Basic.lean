import ClaudeCrypto.Framework.Code

/-!
# A limb-level intermediate language for multi-precision arithmetic

The P-384 code is written and verified once in this small language, then
compiled to each architecture (`Limb/X86.lean`, …); `Framework/Compile.lean`
transfers the proofs along a per-instruction simulation.  So this file is
**not** part of the trusted base: the final theorems are about the machine
code of each architecture.

Registers are fifteen 64-bit variables.  There is one carry flag with the x86
convention (set by additions to the carry, by subtractions to the borrow),
together with a record of which kind of instruction set it, since other
architectures store "not borrow" after a subtraction.  Instructions that would
clobber the flags on some architecture leave the carry undefined, and
branches require it to be undefined.
-/

namespace CC.Limb

/-- The registers. `mulx` multiplies by register `0`. -/
abbrev Var := Fin 15

structure State where
  r : Var → BitVec 64
  /-- carry (after `add`/`adc`) or borrow (after `sub`/`sbb`); `none` if undefined -/
  cf : Option Bool
  /-- whether `cf` was produced by `sub`/`sbb` -/
  sub : Bool
  mem : Mem
  rd : List Region
  wr : List Region
  labels : String → Addr

inductive Instr where
  | mov (d s : Var)
  | movi (d : Var) (v : BitVec 64)
  /-- address of a label plus an offset -/
  | lea (d : Var) (l : String) (off : Nat)
  /-- little-endian 64-bit load from `b + off` -/
  | ld (d b : Var) (off : Nat)
  /-- big-endian 64-bit load from `b + off` -/
  | ldbe (d b : Var) (off : Nat)
  | st (b : Var) (off : Nat) (s : Var)
  /-- `hi:lo := r0 * b` (flags preserved); requires `hi ≠ lo`, `lo ≠ 0`, `lo ≠ b` -/
  | mulx (hi lo b : Var)
  | add (d s : Var)
  | adc (d s : Var)
  | sub (d s : Var)
  | sbb (d s : Var)
  /-- `d := -borrow` (all ones if the last subtraction borrowed); flags preserved -/
  | mask (d : Var)
  | and (d s : Var)
  | or (d s : Var)
  | xor (d s : Var)
  | shr (d : Var) (n : Nat)
  | shl (d : Var) (n : Nat)
  /-- `d := d + n` for a small constant (`n < 2^31`) -/
  | addi (d : Var) (n : Nat)
  /-- `d := d - n` for a small constant (`n < 2^31`) -/
  | subi (d : Var) (n : Nat)
  /-- forget the carry (no machine instruction) -/
  | clrc

inductive Cond where
  | eqz (v : Var)
  | nez (v : Var)

namespace State

def set (s : State) (d : Var) (v : BitVec 64) : State := { s with r := Function.update s.r d v }

def load (s : State) (a : Addr) : Option (BitVec 64) :=
  if InRegions (s.rd ++ s.wr) a 8 then some (s.mem.readW a 64) else none

def store (s : State) (a : Addr) (v : BitVec 64) : Option State :=
  if InRegions s.wr a 8 then some { s with mem := s.mem.writeW a v } else none

end State

/-- Byte-reverse a 64-bit word. -/
def bswap64 (x : BitVec 64) : BitVec 64 :=
  x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8 ++
    x.extractLsb' 32 8 ++ x.extractLsb' 40 8 ++ x.extractLsb' 48 8 ++ x.extractLsb' 56 8

def carryOut (a b : BitVec 64) (c : Bool) : Bool := Nat.ble (2 ^ 64) (a.toNat + b.toNat + c.toNat)
def borrowOut (a b : BitVec 64) (c : Bool) : Bool := Nat.blt a.toNat (b.toNat + c.toNat)

def exec (i : Instr) (s : State) : Option State :=
  match i with
  | .mov d x => some (s.set d (s.r x))
  | .movi d v => some (s.set d v)
  | .lea d l off => some (s.set d (s.labels l + BitVec.ofNat 64 off))
  | .ld d b off => (s.load (s.r b + BitVec.ofNat 64 off)).map fun v => s.set d v
  | .ldbe d b off => (s.load (s.r b + BitVec.ofNat 64 off)).map fun v => s.set d (bswap64 v)
  | .st b off x => s.store (s.r b + BitVec.ofNat 64 off) (s.r x)
  | .mulx hi lo b =>
    if hi = lo ∨ lo = 0 ∨ lo = b then none else
    let p := (s.r 0).toNat * (s.r b).toNat
    some ((s.set lo (BitVec.ofNat 64 p)).set hi (BitVec.ofNat 64 (p / 2 ^ 64)))
  | .add d x =>
    some { s.set d (s.r d + s.r x) with cf := some (carryOut (s.r d) (s.r x) false), sub := false }
  | .adc d x =>
    match s.cf, s.sub with
    | some c, false => some { s.set d (s.r d + s.r x + (BitVec.ofBool c).setWidth 64) with
        cf := some (carryOut (s.r d) (s.r x) c), sub := false }
    | _, _ => none
  | .sub d x =>
    some { s.set d (s.r d - s.r x) with cf := some (borrowOut (s.r d) (s.r x) false), sub := true }
  | .sbb d x =>
    match s.cf, s.sub with
    | some c, true => some { s.set d (s.r d - s.r x - (BitVec.ofBool c).setWidth 64) with
        cf := some (borrowOut (s.r d) (s.r x) c), sub := true }
    | _, _ => none
  | .mask d =>
    match s.cf, s.sub with
    | some c, true => some (s.set d (if c then BitVec.allOnes 64 else 0))
    | _, _ => none
  | .and d x => some { s.set d (s.r d &&& s.r x) with cf := none }
  | .or d x => some { s.set d (s.r d ||| s.r x) with cf := none }
  | .xor d x => some { s.set d (s.r d ^^^ s.r x) with cf := none }
  | .shr d n => if n < 64 then some { s.set d (s.r d >>> n) with cf := none } else none
  | .shl d n => if n < 64 then some { s.set d (s.r d <<< n) with cf := none } else none
  | .addi d n => if n < 2 ^ 31 then some { s.set d (s.r d + BitVec.ofNat 64 n) with cf := none } else none
  | .subi d n => if n < 2 ^ 31 then some { s.set d (s.r d - BitVec.ofNat 64 n) with cf := none } else none
  | .clrc => some { s with cf := none }

def addrs (i : Instr) (s : State) : List Addr :=
  match i with
  | .ld _ b off | .ldbe _ b off | .st b off _ => [s.r b + BitVec.ofNat 64 off]
  | _ => []

def eval (c : Cond) (s : State) : Option Bool :=
  match s.cf with
  | some _ => none
  | none =>
    match c with
    | .eqz v => some (s.r v == 0)
    | .nez v => some (s.r v != 0)

@[reducible] def isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := eval

abbrev Prog := CC.Prog isa

end CC.Limb
