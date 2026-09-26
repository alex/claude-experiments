import ClaudeCrypto.Ppc.Print
import ClaudeCrypto.Spec.SHA256

/-!
# SHA-256 block function, ppc64le with the POWER8 vector crypto instructions

`void cc_sha256_blocks_ppc64le(uint32_t H[8], const uint8_t *data, size_t nblocks)`

In the spirit of OpenSSL's `sha256p8-ppc.pl`: each working variable lives in
ISA `word[0]` of its own vector register (the other three words are
don't-cares), so that one round is a dozen lane-wise vector instructions,
with `vshasigmaw` computing Σ₀/Σ₁ and `vsel` computing Ch/Maj.  Unlike
OpenSSL, the message schedule is computed four words at a time (with
`vshasigmaw` for σ₀/σ₁), and `K + W` is added four words at a time.

Register allocation:
* `r3` = H, `r4` = data (advanced by 64 per block), `r5` = minus the number of
  blocks remaining (counting up to 0),
  `r6`, `r10`, `r11`, `r12` = the round-constant table + 0, 64, 128, 192,
  `r7`, `r8`, `r9` = 16, 32, 48, `r0` = scratch
* `v0`–`v7`: the working variables a…h in `word[0]`, rotating one register per
  round (variable `k` of round `t` is in `varReg t k`)
* `v8`–`v11`: the message schedule, four words each: `W[4k .. 4k+3]` (in
  `word[0 .. 3]`) live in `wreg k = v(8 + k % 4)`
* `v12` = `K + W` for the current group of four rounds; `v13` = that word
  moved to `word[0]`; `v14`, `v15` temporaries
* `v16`, `v17`: the hash value (a, b, c, d) and (e, f, g, h), packed (`word[i]`)
* `v18` = 0, `v19` = the byte-swap permutation

It is a leaf function that uses no nonvolatile register (in particular none of
`v20`–`v31`), no stack and no TOC.
-/

namespace CC.Ppc.SHA256P8

open CC.Ppc

def name : String := "cc_sha256_blocks_ppc64le"

/-- The (local) label of the round-constant table. -/
def kLabel : String := ".Lcc_sha256_ppc64le_K256"

/-- The register holding working variable `k` (0 = a, …, 7 = h) at round `t`. -/
def varReg (t k : Nat) : VReg :=
  match (k + 8 - t % 8) % 8 with
  | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3
  | 4 => .v4 | 5 => .v5 | 6 => .v6 | _ => .v7

/-- The schedule register holding `W[4k .. 4k+3]`. -/
def wreg (k : Nat) : VReg :=
  match k % 4 with
  | 0 => .v8 | 1 => .v9 | 2 => .v10 | _ => .v11

/-- One round `r` (mod 8), with `K + W` in `word[0]` of `kw`:
`h += K + W + Ch(e,f,g); d += h; h += Σ₁(e); d += Σ₁(e); h += Maj(a,b,c) + Σ₀(a)`
(ordered so that the new `e` is available one addition after `Σ₁(e)`). -/
def roundCode (r : Nat) (kw : VReg) : List Instr :=
  let a := varReg r 0; let b := varReg r 1; let c := varReg r 2; let d := varReg r 3
  let e := varReg r 4; let f := varReg r 5; let g := varReg r 6; let h := varReg r 7
  [ .vadduwm h h kw,
    .vsel .v14 g f e,
    .vshasigmaw .v15 e true 15,
    .vadduwm h h .v14,
    .vxor .v14 a b,
    .vadduwm d d h,
    .vsel .v14 b c .v14,
    .vadduwm h h .v15,
    .vadduwm d d .v15,
    .vshasigmaw .v15 a true 0,
    .vadduwm h h .v14,
    .vadduwm h h .v15 ]

/-- Round `r` (mod 8) of a group: `K + W` for round `4j + r % 4` is `word[r % 4]` of `v12`. -/
def stepCode (r : Nat) : List Instr :=
  if r % 4 = 0 then roundCode r .v12
  else .vsldoi .v13 .v12 .v12 (4 * (r % 4)) :: roundCode r .v13

/-- The next four schedule words `W[4k+16 .. 4k+19]`, from `wreg k` … `wreg (k+3)`,
into `wreg k` (using `v18 = 0` and `σ₁(0) = 0`). -/
def schedCode (p : Nat) : List Instr :=
  let xa := wreg p; let xb := wreg (p + 1); let xc := wreg (p + 2); let xd := wreg (p + 3)
  [ .vsldoi .v14 xa xb 4,             -- W[t-15 .. t-12]
    .vshasigmaw .v14 .v14 false 0,    -- σ₀
    .vadduwm xa xa .v14,
    .vsldoi .v14 xc xd 4,             -- W[t-7 .. t-4]
    .vadduwm xa xa .v14,
    .vsldoi .v14 xd .v18 8,           -- W[t-2], W[t-1], 0, 0
    .vshasigmaw .v14 .v14 false 15,   -- σ₁
    .vadduwm xa xa .v14,              -- W[t], W[t+1] done
    .vsldoi .v14 .v18 xa 8,           -- 0, 0, W[t], W[t+1]
    .vshasigmaw .v14 .v14 false 15,   -- σ₁
    .vadduwm xa xa .v14 ]             -- W[t+2], W[t+3] done

/-- `EA = (RA|0) + (RB)` of the round constants `K[4j .. 4j+3]`. -/
def kRegs (j : Nat) : GReg × GReg :=
  let base : GReg := match j / 4 with
    | 0 => .r6 | 1 => .r10 | 2 => .r11 | _ => .r12
  match j % 4 with
  | 0 => (.r0, base) | 1 => (base, .r7) | 2 => (base, .r8) | _ => (base, .r9)

/-- Load `K[4j .. 4j+3]`, compute `v12 = K + W` for the group, and (if `sched`)
the schedule words for group `j + 4`. -/
def headCode (p : Nat) (ra rb : GReg) (sched : Bool) : List Instr :=
  [ .lxvw4x .v14 ra rb, .vadduwm .v12 (wreg p) .v14 ] ++ (if sched then schedCode p else [])

/-- Rounds `4j .. 4j+3`. -/
def groupCode (j : Nat) : List Instr :=
  headCode (j % 4) (kRegs j).1 (kRegs j).2 (Nat.blt j 12) ++
    stepCode (4 * (j % 2)) ++ stepCode (4 * (j % 2) + 1) ++ stepCode (4 * (j % 2) + 2) ++
    stepCode (4 * (j % 2) + 3)

def groups : List Instr := ((List.range 16).map groupCode).flatten

/-- Unpack the hash value into the working variables. -/
def unpack : List Instr :=
  [ .vor .v0 .v16 .v16, .vsldoi .v1 .v16 .v16 4, .vsldoi .v2 .v16 .v16 8, .vsldoi .v3 .v16 .v16 12,
    .vor .v4 .v17 .v17, .vsldoi .v5 .v17 .v17 4, .vsldoi .v6 .v17 .v17 8, .vsldoi .v7 .v17 .v17 12 ]

/-- Load the message block (big-endian words), advance `r4`. -/
def loadMsg : List Instr :=
  [ .lxvw4x .v8 .r0 .r4, .lxvw4x .v9 .r4 .r7, .lxvw4x .v10 .r4 .r8, .lxvw4x .v11 .r4 .r9,
    .vperm .v8 .v8 .v8 .v19, .vperm .v9 .v9 .v9 .v19, .vperm .v10 .v10 .v10 .v19,
    .vperm .v11 .v11 .v11 .v19, .addi .r4 .r4 64 ]

/-- Pack the working variables, add them into the hash value, count the block. -/
def finish : List Instr :=
  [ .vmrghw .v13 .v0 .v1, .vmrghw .v14 .v2 .v3, .xxpermdi .v13 .v13 .v14 0,
    .vmrghw .v14 .v4 .v5, .vmrghw .v15 .v6 .v7, .xxpermdi .v14 .v14 .v15 0,
    .vadduwm .v16 .v16 .v13, .vadduwm .v17 .v17 .v14,
    .addi .r5 .r5 1, .cmpldi .r5 0 ]

/-- The body of the per-block loop. -/
def blockCode : List Instr := unpack ++ loadMsg ++ groups ++ finish

def setup : List Instr :=
  [ .neg .r5 .r5, .adr .r6 kLabel, .addi .r10 .r6 64, .addi .r11 .r6 128, .addi .r12 .r6 192,
    .addi .r0 .r6 256, .addi .r7 .r0 16, .addi .r8 .r0 32, .addi .r9 .r0 48,
    .lxvw4x .v19 .r0 .r0, .vxor .v18 .v18 .v18,
    .lxvw4x .v16 .r0 .r3, .lxvw4x .v17 .r3 .r7 ]

def storeState : List Instr := [ .stxvw4x .v16 .r0 .r3, .stxvw4x .v17 .r3 .r7 ]

def code : Prog :=
  .seq (.block [.cmpldi .r5 0])
    (.ite .eq (.block [])
      (.seq (.block setup) (.seq (.loop (.block blockCode) .ne) (.block storeState))))

/-- The byte-swap permutation for `vperm` (as loaded by `lxvw4x`): ISA bytes
`3,2,1,0, 7,6,5,4, 11,10,9,8, 15,14,13,12`. -/
def bswapMask : List (BitVec 32) := [0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c]

/-- The data table: the round constants (FIPS 180-4 §4.2.2), then the byte-swap mask. -/
def table : List (BitVec 32) := Spec.SHA256.K ++ bswapMask

def kTable : List String :=
  ["\t.p2align 4", kLabel ++ ":"] ++
  ((List.range 17).map fun i =>
    "\t.long " ++ ",".intercalate ((List.range 4).map fun j => "0x" ++ (table[4 * i + j]!).toHex))

def asm : String := (printer kTable).function name code

end CC.Ppc.SHA256P8
