import ClaudeCrypto.X86.Print
import ClaudeCrypto.Spec.SHA256

/-!
# SHA-256 block function, x86-64 AVX2 + BMI1/BMI2 implementation

`void cc_sha256_blocks_x86_avx2(uint32_t H[8], const uint8_t *data, size_t nblocks)`

Blocks are processed in pairs (a single block when the remaining count is
odd).  The message schedules of both blocks are computed together in the two
128-bit lanes of the `ymm` registers; `W[t] + K[t]` for both blocks is kept in
a 512-byte stack buffer (`[rsp + 32⌊t/4⌋ + 4(t mod 4) + 16·lane]`).  The rounds
of the first block interleave the schedule computation (one quarter of a
four-word schedule group after each round); the rounds of the second block
then read the precomputed values.

Registers: `rdi` = H, `rsi` = data, `rdx` = blocks remaining;
working variables in `r8d..r15d` (rotating one register per round);
`eax, ebx, ecx, ebp` are temporaries (`ebx`/`ecx` alternate as `a^b`/`b^c`,
`ebp` carries `Σ₀(a)` into the next round, where it is added to the new `a`);
`ymm0–ymm3` hold the last sixteen schedule words, `ymm4–ymm7` scratch,
`ymm10–ymm12` shuffle masks.
-/

namespace CC.X86.SHA256Avx2

open CC.X86

/-! ## Constant tables -/

/-- Little-endian bytes of a list of words. -/
def wordsLE (ws : List (BitVec 32)) : List (BitVec 8) :=
  ws.flatMap fun w => [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- `K`, each group of four words duplicated for the two lanes (512 bytes). -/
def kTable : List (BitVec 8) :=
  wordsLE ((List.range 16).flatMap fun g =>
    let ks := (List.range 4).map fun j => Spec.SHA256.K[4 * g + j]!
    ks ++ ks)

/-- `vpshufb` mask reversing the bytes of every dword. -/
def bswapMask : List (BitVec 8) :=
  (List.range 32).map fun i => BitVec.ofNat 8 ((i / 4) * 4 + 3 - i % 4)

/-- `vpshufb` mask moving dwords 0,2 to 0,1 and zeroing dwords 2,3 (per lane). -/
def shuf00BA : List (BitVec 8) :=
  let l : List Nat := [0, 1, 2, 3, 8, 9, 10, 11, 128, 128, 128, 128, 128, 128, 128, 128]
  (l ++ l).map (BitVec.ofNat 8)

/-- `vpshufb` mask moving dwords 0,2 to 2,3 and zeroing dwords 0,1 (per lane). -/
def shufDC00 : List (BitVec 8) :=
  let l : List Nat := [128, 128, 128, 128, 128, 128, 128, 128, 0, 1, 2, 3, 8, 9, 10, 11]
  (l ++ l).map (BitVec.ofNat 8)

def kLabel : String := ".Lcc_sha256_avx2_K"
def bswapLabel : String := ".Lcc_sha256_avx2_bswap"
def s00BALabel : String := ".Lcc_sha256_avx2_00BA"
def sDC00Label : String := ".Lcc_sha256_avx2_DC00"

def dataTables : List (String × List (BitVec 8)) :=
  [(kLabel, kTable), (bswapLabel, bswapMask), (s00BALabel, shuf00BA), (sDC00Label, shufDC00)]

/-! ## Registers -/

def stReg : Nat → Reg
  | 0 => .r8 | 1 => .r9 | 2 => .r10 | 3 => .r11 | 4 => .r12 | 5 => .r13 | 6 => .r14 | _ => .r15

/-- The register holding working variable `k` (0 = a, …, 7 = h) at round `t`. -/
def varReg (t k : Nat) : Reg := stReg ((k + 8 - t % 8) % 8)

/-- `a^b` of the current round is computed into `tY t`; `tZ t` holds `b^c`. -/
def tY (t : Nat) : Reg := if t % 2 = 0 then .rbx else .rcx
def tZ (t : Nat) : Reg := if t % 2 = 0 then .rcx else .rbx

def ymm : Nat → VReg
  | 0 => .y0 | 1 => .y1 | 2 => .y2 | 3 => .y3 | 4 => .y4 | 5 => .y5 | 6 => .y6 | 7 => .y7
  | 8 => .y8 | 9 => .y9 | 10 => .y10 | 11 => .y11 | 12 => .y12 | 13 => .y13 | 14 => .y14 | _ => .y15

def rspAt (off : Nat) : MemOp := { base := .rsp, disp := (off : Int) }
def ripAt (l : String) (off : Nat) : MemOp := { rip := some l, disp := (off : Int) }

/-! ## One round -/

/-- Offset of `W[t] + K[t]` of lane `L` in the stack buffer. -/
def wkOff (L t : Nat) : Nat := 32 * (t / 4) + 4 * (t % 4) + 16 * L

/-- Round `t` of lane `L`.  On entry `ebp` holds `Σ₀` of the previous round's `a`
(zero before round 0), which is added to this round's `a` first. -/
def roundCode (L t : Nat) : List Instr :=
  let a := varReg t 0; let b := varReg t 1; let d := varReg t 3
  let e := varReg t 4; let f := varReg t 5; let g := varReg t 6; let h := varReg t 7
  let X := Reg.rax; let Y := tY t; let Z := tZ t; let W := Reg.rbp
  [ .alu .add .d h (.mem (rspAt (wkOff L t))),   -- h += W[t] + K[t]
    .alu .add .d a (.reg W),                      -- a += Σ₀ (deferred from the previous round)
    .mov .d Y (.reg f),
    .alu .and .d Y (.reg e),                      -- e & f
    .andn .d X e (.reg g),                        -- ~e & g
    .alu .add .d d (.reg h),
    .alu .add .d Y (.reg X),                      -- Ch(e,f,g)
    .rorx .d X e 6,
    .alu .add .d d (.reg Y),
    .alu .add .d h (.reg Y),
    .rorx .d Y e 11,
    .alu .xor .d X (.reg Y),
    .rorx .d Y e 25,
    .alu .xor .d X (.reg Y),                      -- Σ₁(e)
    .alu .add .d d (.reg X),                      -- d + T₁  (the new e)
    .alu .add .d h (.reg X),                      -- T₁
    .mov .d Y (.reg a),
    .alu .xor .d Y (.reg b),                      -- a ^ b   (b ^ c of the next round)
    .alu .and .d Z (.reg Y),
    .alu .xor .d Z (.reg b),                      -- Maj(a,b,c) = ((a^b) & (b^c)) ^ b
    .alu .add .d h (.reg Z),                      -- T₁ + Maj
    .rorx .d X a 2,
    .rorx .d W a 13,
    .alu .xor .d W (.reg X),
    .rorx .d X a 22,
    .alu .xor .d W (.reg X) ]                     -- Σ₀(a), added at the start of the next round

/-! ## Message schedule -/

/-- Quarter `q` of the computation of schedule group `g` (words `4g … 4g+3`),
from the window `ymm[g%4] … ymm[(g+3)%4]` holding words `4g-16 … 4g-1`. -/
def schedSlice (g q : Nat) : List Instr :=
  let x0 := ymm (g % 4); let x1 := ymm ((g + 1) % 4); let x2 := ymm ((g + 2) % 4); let x3 := ymm ((g + 3) % 4)
  match q with
  | 0 =>
    [ .vpalignr .y4 x1 x0 4,              -- W[t-15 .. t-12]
      .vpalignr .y7 x3 x2 4,              -- W[t-7 .. t-4]
      .vpaddd x0 x0 (.reg .y7),           -- W[t-16] + W[t-7]
      .vpsrld .y7 .y4 7,
      .vpslld .y5 .y4 25,
      .vpxor .y7 .y7 .y5,
      .vpsrld .y5 .y4 18,
      .vpxor .y7 .y7 .y5,
      .vpslld .y5 .y4 14,
      .vpxor .y7 .y7 .y5,
      .vpsrld .y5 .y4 3,
      .vpxor .y7 .y7 .y5,                 -- σ₀(W[t-15 ..])
      .vpaddd x0 x0 (.reg .y7) ]
  | 1 =>
    [ .vpshufd .y6 x3 0xfa,               -- W[t-2] W[t-2] W[t-1] W[t-1]
      .vpsrld .y7 .y6 10,
      .vpsrlq .y5 .y6 17,
      .vpxor .y7 .y7 .y5,
      .vpsrlq .y5 .y6 19,
      .vpxor .y7 .y7 .y5,                 -- σ₁ in dwords 0 and 2
      .vpshufb .y7 .y7 .y10,              -- move to dwords 0,1
      .vpaddd x0 x0 (.reg .y7) ]          -- W[t], W[t+1] done
  | 2 =>
    [ .vpshufd .y6 x0 0x50,               -- W[t] W[t] W[t+1] W[t+1]
      .vpsrld .y7 .y6 10,
      .vpsrlq .y5 .y6 17,
      .vpxor .y7 .y7 .y5,
      .vpsrlq .y5 .y6 19,
      .vpxor .y7 .y7 .y5,
      .vpshufb .y7 .y7 .y11,              -- move to dwords 2,3
      .vpaddd x0 x0 (.reg .y7) ]          -- W[t+2], W[t+3] done
  | _ =>
    [ .vpaddd .y4 x0 (.mem (ripAt kLabel (32 * g))),
      .vstore256 (rspAt (32 * g)) .y4 ]

/-! ## Lanes -/

/-- Round `t` of the first lane, followed by a quarter of a schedule group. -/
def lane0Round (t : Nat) : List Instr :=
  roundCode 0 t ++ (if t < 48 then schedSlice (t / 4 + 4) (t % 4) else [])

def hReg (k : Nat) : Reg := varReg 0 k

/-- Add the working variables into the hash value in memory. -/
def addH : List Instr :=
  ((List.range 8).map fun k =>
    [ .alu .add .d (hReg k) (.mem { base := .rdi, disp := ((4 * k : Nat) : Int) }),
      .store .d { base := .rdi, disp := ((4 * k : Nat) : Int) } (hReg k) ]).flatten

/-- Before the rounds: `b ^ c` into the first `tZ`, clear the deferred `Σ₀`. -/
def laneInit : List Instr :=
  [ .mov .d (tZ 0) (.reg (varReg 0 1)), .alu .xor .d (tZ 0) (.reg (varReg 0 2)),
    .alu .xor .d .rbp (.reg .rbp) ]

/-- After the rounds: the last deferred `Σ₀`, then add into the hash value. -/
def laneFinish : List Instr :=
  [ .alu .add .d (varReg 64 0) (.reg .rbp) ] ++ addH

def lane0 : List Instr := laneInit ++ ((List.range 64).map lane0Round).flatten ++ laneFinish
def lane1 : List Instr := laneInit ++ ((List.range 64).map (roundCode 1)).flatten ++ laneFinish

/-! ## Loading and preparing the message -/

def load2 : List Instr :=
  ((List.range 4).map fun j =>
    [ .vload128 (ymm j) { base := .rsi, disp := ((16 * j : Nat) : Int) },
      .vinserti128hi (ymm j) (ymm j) { base := .rsi, disp := ((64 + 16 * j : Nat) : Int) } ]).flatten

def load1 : List Instr :=
  (List.range 4).map fun j => .vbroadcasti128 (ymm j) { base := .rsi, disp := ((16 * j : Nat) : Int) }

/-- Byte-swap the message words, store `W + K` for words 0–15. -/
def prep : List Instr :=
  ((List.range 4).map fun j =>
    [ .vpshufb (ymm j) (ymm j) .y12,
      .vpaddd .y4 (ymm j) (.mem (ripAt kLabel (32 * j))),
      .vstore256 (rspAt (32 * j)) .y4 ]).flatten

def setup : List Instr :=
  [ .vload256 .y12 (ripAt bswapLabel 0),
    .vload256 .y10 (ripAt s00BALabel 0),
    .vload256 .y11 (ripAt sDC00Label 0) ] ++
  (List.range 8).map fun k => .mov .d (hReg k) (.mem { base := .rdi, disp := ((4 * k : Nat) : Int) })

def prologue : List Instr :=
  [ .push .rbx, .push .rbp, .push .r12, .push .r13, .push .r14, .push .r15,
    .alu .sub .q .rsp (.imm 512),
    .alu .test .q .rdx (.reg .rdx) ]

def epilogue : List Instr :=
  [ .vzeroupper,
    .alu .add .q .rsp (.imm 512),
    .pop .r15, .pop .r14, .pop .r13, .pop .r12, .pop .rbp, .pop .rbx ]

def parity : List Instr := [ .alu .test .d .rdx (.imm 1) ]

/-- One iteration: one block if the remaining count is odd, otherwise two. -/
def body : Prog :=
  .seq (.block parity)
  (.seq (.ite .ne (.block load1) (.block load2))
  (.seq (.block (prep ++ lane0 ++ parity))
        (.ite .ne
          (.block [ .alu .add .q .rsi (.imm 64), .alu .sub .q .rdx (.imm 1) ])
          (.block (lane1 ++ [ .alu .add .q .rsi (.imm 128), .alu .sub .q .rdx (.imm 2) ])))))

def code : Prog :=
  .seq (.block prologue)
    (.seq (.ite .e (.block []) (.seq (.block setup) (.loop body .ne)))
      (.block epilogue))

def name : String := "cc_sha256_blocks_x86_avx2"

def asm : String := printer.function name code

end CC.X86.SHA256Avx2
