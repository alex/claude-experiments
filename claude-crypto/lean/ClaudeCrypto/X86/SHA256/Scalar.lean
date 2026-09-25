import ClaudeCrypto.X86.Print
import ClaudeCrypto.Spec.SHA256

/-!
# SHA-256 block function, x86-64 scalar (BMI1/BMI2) implementation

`void cc_sha256_blocks_x86_scalar(uint32_t H[8], const uint8_t *data, size_t nblocks)`

Register allocation:
* `rdi` = H, `rsi` = data (advanced by 64 per block), `rdx` = blocks remaining
* working variables a..h live in `r8d..r15d`, rotating one register per round
* `eax, ebx, ecx, ebp` are temporaries
* the message schedule is a 16-word circular buffer at `[rsp]`
-/

namespace CC.X86.SHA256Scalar

open CC.X86

/-- The register holding working variable `k` (0 = a, …, 7 = h) at round `t`. -/
def varReg (t k : Nat) : Reg :=
  match (k + 8 - t % 8) % 8 with
  | 0 => .r8 | 1 => .r9 | 2 => .r10 | 3 => .r11
  | 4 => .r12 | 5 => .r13 | 6 => .r14 | _ => .r15

def slot (j : Nat) : MemOp := { base := .rsp, disp := 4 * (j % 16) }

/-- Round `t`: `h += Σ₁(e) + Ch(e,f,g) + Kₜ + Wₜ; d += h; h += Σ₀(a) + Maj(a,b,c)`. -/
def roundCode (t : Nat) : List Instr :=
  let a := varReg t 0; let b := varReg t 1; let c := varReg t 2; let d := varReg t 3
  let e := varReg t 4; let f := varReg t 5; let g := varReg t 6; let h := varReg t 7
  [ .alu .add .d h (.mem (slot t)),
    .alu .add .d h (.imm (Spec.SHA256.K[t]!)),
    .rorx .d .rax e 6,
    .rorx .d .rbx e 11,
    .alu .xor .d .rax (.reg .rbx),
    .rorx .d .rbx e 25,
    .alu .xor .d .rax (.reg .rbx),
    .alu .add .d h (.reg .rax),
    .andn .d .rbx e (.reg g),
    .mov .d .rcx (.reg f),
    .alu .and .d .rcx (.reg e),
    .alu .add .d h (.reg .rbx),
    .alu .add .d h (.reg .rcx),
    .alu .add .d d (.reg h),
    .rorx .d .rax a 2,
    .rorx .d .rbx a 13,
    .alu .xor .d .rax (.reg .rbx),
    .rorx .d .rbx a 22,
    .alu .xor .d .rax (.reg .rbx),
    .alu .add .d h (.reg .rax),
    .mov .d .rbx (.reg b),
    .mov .d .rcx (.reg b),
    .alu .xor .d .rbx (.reg c),
    .alu .and .d .rcx (.reg c),
    .alu .and .d .rbx (.reg a),
    .alu .xor .d .rbx (.reg .rcx),
    .alu .add .d h (.reg .rbx) ]

/-- Message schedule for `t ≥ 16`: `W[t%16] += σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15])`. -/
def schedCode (t : Nat) : List Instr :=
  [ .mov .d .rax (.mem (slot (t + 1))),
    .rorx .d .rbx .rax 7,
    .rorx .d .rcx .rax 18,
    .alu .xor .d .rbx (.reg .rcx),
    .shift .shr .d .rax 3,
    .alu .xor .d .rbx (.reg .rax),
    .mov .d .rax (.mem (slot (t + 14))),
    .rorx .d .rcx .rax 17,
    .rorx .d .rbp .rax 19,
    .alu .xor .d .rcx (.reg .rbp),
    .shift .shr .d .rax 10,
    .alu .xor .d .rcx (.reg .rax),
    .alu .add .d .rbx (.reg .rcx),
    .alu .add .d .rbx (.mem (slot (t + 9))),
    .alu .add .d .rbx (.mem (slot t)),
    .store .d (slot t) .rbx ]

/-- Load message word `j` (big-endian) into the schedule buffer. -/
def loadCode (j : Nat) : List Instr :=
  [ .movbe .d .rax { base := .rsi, disp := 4 * j },
    .store .d (slot j) .rax ]

def hReg (k : Nat) : Reg := varReg 0 k

/-- The body of the per-block loop. -/
def blockCode : List Instr :=
  ((List.range 16).map loadCode).flatten ++
  ((List.range 16).map roundCode).flatten ++
  ((List.range 48).map fun i => schedCode (i + 16) ++ roundCode (i + 16)).flatten ++
  ((List.range 8).map fun k =>
    [ .alu .add .d (hReg k) (.mem { base := .rdi, disp := 4 * k }),
      .store .d { base := .rdi, disp := 4 * k } (hReg k) ]).flatten ++
  [ .alu .add .q .rsi (.imm 64),
    .dec .q .rdx ]

def prologue : List Instr :=
  [ .push .rbx, .push .rbp, .push .r12, .push .r13, .push .r14, .push .r15,
    .alu .sub .q .rsp (.imm 64),
    .alu .test .q .rdx (.reg .rdx) ]

def loadState : List Instr :=
  (List.range 8).map fun k => .mov .d (hReg k) (.mem { base := .rdi, disp := 4 * k })

def epilogue : List Instr :=
  [ .alu .add .q .rsp (.imm 64),
    .pop .r15, .pop .r14, .pop .r13, .pop .r12, .pop .rbp, .pop .rbx ]

def code : Prog :=
  .seq (.block prologue)
    (.seq (.ite .e (.block []) (.seq (.block loadState) (.loop (.block blockCode) .ne)))
      (.block epilogue))

def name : String := "cc_sha256_blocks_x86_scalar"

def asm : String := printer.function name code

end CC.X86.SHA256Scalar
