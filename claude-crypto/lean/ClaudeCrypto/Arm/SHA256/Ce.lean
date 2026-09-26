import ClaudeCrypto.Arm.Print
import ClaudeCrypto.Spec.SHA256

/-!
# SHA-256 block function, AArch64 with the SHA-256 crypto extension

`void cc_sha256_blocks_arm(uint32_t H[8], const uint8_t *data, size_t nblocks)`

In the style of OpenSSL's `sha256_block_armv8`.  Register allocation:
* `x0` = H, `x1` = data (advanced by 64 per block), `x2` = blocks remaining,
  `x3` = address of the round-constant table
* `v0` = (a, b, c, d), `v1` = (e, f, g, h) (element 0 = a resp. e); `v2` is a
  copy of `v0` for `sha256h2`
* `v4`–`v7`: the message schedule, four words each; the words `W[4k .. 4k+3]`
  live in `v(4 + k % 4)`
* `v16` = `K + W` for the current group of four rounds
* `v18`, `v19`: the hash value at the start of the block

It is a leaf function that uses no callee-saved register (in particular none
of `v8`–`v15`) and no stack.
-/

namespace CC.Arm.SHA256Ce

open CC.Arm

def name : String := "cc_sha256_blocks_arm"

/-- The (local) label of the round-constant table. -/
def kLabel : String := ".Lcc_sha256_arm_K256"

/-- The schedule register holding `W[4k .. 4k+3]`. -/
def wreg (k : Nat) : VReg :=
  match k % 4 with
  | 0 => .v4 | 1 => .v5 | 2 => .v6 | _ => .v7

/-- Four rounds with the schedule registers rotated by `p`, the round
constants at offset `off` of the table, and (if `sched`) the computation of
the next four schedule words. -/
def groupCodeP (p off : Nat) (sched : Bool) : List Instr :=
  [ .ldrq .v16 .x3 off,
    .addv .v16 .v16 (wreg p) ] ++
  (if sched then [.sha256su0 (wreg p) (wreg (p + 1))] else []) ++
  [ .movv .v2 .v0,
    .sha256h .v0 .v1 .v16,
    .sha256h2 .v1 .v2 .v16 ] ++
  (if sched then [.sha256su1 (wreg p) (wreg (p + 2)) (wreg (p + 3))] else [])

/-- Rounds `4g .. 4g+3`. -/
def groupCode (g : Nat) : List Instr := groupCodeP (g % 4) (16 * g) (Nat.blt g 12)

def groups : List Instr := ((List.range 16).map groupCode).flatten

/-- Load the message block (big-endian words), advance `x1`, save the hash value. -/
def loadMsg : List Instr :=
  [ .ld1 [.v4, .v5, .v6, .v7] .b16 .x1 true,
    .rev32 .v4 .v4, .rev32 .v5 .v5, .rev32 .v6 .v6, .rev32 .v7 .v7,
    .movv .v18 .v0, .movv .v19 .v1 ]

/-- Add the saved hash value, count down. -/
def finish : List Instr := [ .addv .v0 .v0 .v18, .addv .v1 .v1 .v19, .subi .x2 .x2 1 ]

/-- The body of the per-block loop. -/
def blockCode : List Instr := loadMsg ++ groups ++ finish

def loadState : List Instr := [ .ld1 [.v0, .v1] .s4 .x0 false, .adr .x3 kLabel ]

def storeState : List Instr := [ .st1 [.v0, .v1] .s4 .x0 false ]

def code : Prog :=
  .ite (.cbz .x2) (.block [])
    (.seq (.block loadState) (.seq (.loop (.block blockCode) (.cbnz .x2)) (.block storeState)))

/-- The round-constant table (FIPS 180-4 §4.2.2), emitted after the function. -/
def kTable : List String :=
  ["\t.p2align 6", kLabel ++ ":"] ++
  ((List.range 16).map fun i =>
    "\t.long " ++ ", ".intercalate
      ((List.range 4).map fun j => "0x" ++ (Spec.SHA256.K[4 * i + j]!).toHex))

def asm : String := (printer kTable).function name code

end CC.Arm.SHA256Ce
