import ClaudeCrypto.X86.Print
import ClaudeCrypto.Spec.SHA256

/-!
# SHA-256 block function, x86-64 with the SHA extensions (SHA-NI)

`void cc_sha256_blocks_x86_shani(uint32_t H[8], const uint8_t *data, size_t nblocks)`

In the style of OpenSSL's `sha256_block_data_order_shaext`.  Uses only
legacy-SSE encodings (SSSE3 `pshufb`/`palignr`, SHA-NI).  Register allocation:
* `rdi` = H, `rsi` = data (advanced by 64 per block), `rdx` = blocks remaining
* `xmm1` = (F, E, B, A), `xmm2` = (H, G, D, C) (element 0 first), the operand
  layout of `sha256rnds2`; after each `sha256rnds2` the two registers swap roles
* `xmm0` = `K + W` for the current two rounds (the implicit operand of `sha256rnds2`)
* `xmm3`–`xmm6`: the message schedule, four words each; `W[4k .. 4k+3]` lives in
  `xmm(3 + k % 4)`
* `xmm7` scratch, `xmm8` the byte-swap mask, `xmm9`/`xmm10` the hash value at
  the start of the block

It is a leaf function that uses no stack and no callee-saved register (every
`xmm` register is caller-saved in the System V ABI).
-/

namespace CC.X86.SHA256ShaNi

open CC.X86

/-! ## Constant tables -/

/-- Little-endian bytes of a list of words. -/
def wordsLE (ws : List (BitVec 32)) : List (BitVec 8) :=
  ws.flatMap fun w => [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- The round constants `K` (256 bytes). -/
def kTable : List (BitVec 8) := wordsLE Spec.SHA256.K

/-- `pshufb` mask reversing the bytes of every dword. -/
def bswapMask : List (BitVec 8) :=
  (List.range 16).map fun i => BitVec.ofNat 8 ((i / 4) * 4 + 3 - i % 4)

def kLabel : String := ".Lcc_sha256_shani_K"
def bswapLabel : String := ".Lcc_sha256_shani_bswap"

def dataTables : List (String × List (BitVec 8)) := [(kLabel, kTable), (bswapLabel, bswapMask)]

/-! ## Code -/

def ripAt (l : String) (off : Nat) : MemOp := { rip := some l, disp := (off : Int) }

/-- The schedule register holding `W[4k .. 4k+3]`. -/
def wreg (k : Nat) : VReg :=
  match k % 4 with
  | 0 => .y3 | 1 => .y4 | 2 => .y5 | _ => .y6

/-- Four rounds with the schedule registers rotated by `p`, the round constants at
offset `off` of the table; `fin`: finish the schedule words of the next group
(`palignr` + `sha256msg2`); `m1`: start those of the group after next but two
(`sha256msg1`). -/
def groupCodeP (p off : Nat) (fin m1 : Bool) : List Instr :=
  [ .movdquLd .y0 (ripAt kLabel off),
    .paddd .y0 (wreg p),
    .sha256rnds2 .y2 .y1 ] ++
  (if fin then
    [ .movdqa .y7 (wreg p),
      .palignr .y7 (wreg (p + 3)) 4,
      .paddd (wreg (p + 1)) .y7,
      .sha256msg2 (wreg (p + 1)) (wreg p) ] else []) ++
  [ .pshufd .y0 .y0 0x0e,
    .sha256rnds2 .y1 .y2 ] ++
  (if m1 then [ .sha256msg1 (wreg (p + 3)) (wreg p) ] else [])

/-- Rounds `4g .. 4g+3`. -/
def groupCode (g : Nat) : List Instr :=
  groupCodeP (g % 4) (16 * g) (Nat.ble 3 g && Nat.ble g 14) (Nat.ble 1 g && Nat.ble g 12)

def groups : List Instr := ((List.range 16).map groupCode).flatten

/-- Load the message block (big-endian words), save the hash value. -/
def loadMsg : List Instr :=
  [ .movdquLd .y3 { base := .rsi, disp := 0 },
    .movdquLd .y4 { base := .rsi, disp := 16 },
    .movdquLd .y5 { base := .rsi, disp := 32 },
    .movdquLd .y6 { base := .rsi, disp := 48 },
    .pshufb .y3 .y8, .pshufb .y4 .y8, .pshufb .y5 .y8, .pshufb .y6 .y8,
    .movdqa .y9 .y1, .movdqa .y10 .y2 ]

/-- Add the saved hash value, advance the data pointer, count down. -/
def finish : List Instr :=
  [ .paddd .y1 .y9, .paddd .y2 .y10,
    .lea .q .rsi { base := .rsi, disp := 64 },
    .alu .sub .q .rdx (.imm 1) ]

/-- The body of the per-block loop. -/
def blockCode : List Instr := loadMsg ++ groups ++ finish

/-- Load the hash value `(A..D), (E..H)` and rearrange it into `(F,E,B,A), (H,G,D,C)`. -/
def loadState : List Instr :=
  [ .movdquLd .y1 { base := .rdi, disp := 0 },
    .movdquLd .y2 { base := .rdi, disp := 16 },
    .movdquLd .y8 (ripAt bswapLabel 0),
    .pshufd .y7 .y1 0x1b,          -- D C B A
    .pshufd .y2 .y2 0x1b,          -- H G F E
    .movdqa .y1 .y2,
    .punpckhqdq .y1 .y7,           -- F E B A
    .punpcklqdq .y2 .y7 ]          -- H G D C

/-- Rearrange and store the hash value. -/
def storeState : List Instr :=
  [ .movdqa .y7 .y2,
    .punpckhqdq .y7 .y1,           -- D C B A
    .punpcklqdq .y2 .y1,           -- H G F E
    .pshufd .y7 .y7 0x1b,          -- A B C D
    .pshufd .y2 .y2 0x1b,          -- E F G H
    .movdquSt { base := .rdi, disp := 0 } .y7,
    .movdquSt { base := .rdi, disp := 16 } .y2 ]

def code : Prog :=
  .seq (.block [.alu .test .q .rdx (.reg .rdx)])
    (.ite .e (.block [])
      (.seq (.block loadState) (.seq (.loop (.block blockCode) .ne) (.block storeState))))

def name : String := "cc_sha256_blocks_x86_shani"

def asm : String := printer.function name code

end CC.X86.SHA256ShaNi
