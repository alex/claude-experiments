import Mathlib.Tactic
import Mathlib.Data.BitVec

/-!
# SHA-256 specification (FIPS 180-4)

This file is the *reviewable* definition of SHA-256 that all implementations
are proven against.  It is a direct transcription of FIPS PUB 180-4
("Secure Hash Standard", August 2015); section numbers refer to that
document.  It deliberately makes no attempt at efficiency.

A `Word` is a 32-bit value.  All addition is modulo 2^32 (§3.2).
-/

namespace CC.Spec.SHA256

abbrev Word := BitVec 32

/-! ## §2.2.2 / §3.2 Operations on words -/

/-- ROTR^n(x): rotate right by `n` bits. -/
def ROTR (n : Nat) (x : Word) : Word := x.rotateRight n

/-- SHR^n(x): shift right by `n` bits. -/
def SHR (n : Nat) (x : Word) : Word := x >>> n

/-! ## §4.1.2 SHA-224 and SHA-256 functions -/

def Ch (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)
def Maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
/-- Σ₀²⁵⁶ -/
def SIGMA0 (x : Word) : Word := ROTR 2 x ^^^ ROTR 13 x ^^^ ROTR 22 x
/-- Σ₁²⁵⁶ -/
def SIGMA1 (x : Word) : Word := ROTR 6 x ^^^ ROTR 11 x ^^^ ROTR 25 x
/-- σ₀²⁵⁶ -/
def sigma0 (x : Word) : Word := ROTR 7 x ^^^ ROTR 18 x ^^^ SHR 3 x
/-- σ₁²⁵⁶ -/
def sigma1 (x : Word) : Word := ROTR 17 x ^^^ ROTR 19 x ^^^ SHR 10 x

/-! ## §4.2.2 SHA-224 and SHA-256 constants -/

def K : List Word := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-! ## §5.3.3 Initial hash value -/

def H0 : List Word := [
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-! ## §5.1.1 Padding the message

The message is a list of bytes (so its length in bits, `ℓ`, is a multiple
of 8).  Append the bit "1" (the byte 0x80), then `k` zero bits where
`ℓ + 1 + k ≡ 448 (mod 512)` (so whole zero bytes here), then `ℓ` as a
64-bit big-endian integer. -/

def pad (msg : List (BitVec 8)) : List (BitVec 8) :=
  let ℓ := 8 * msg.length
  -- the number of zero bytes: the least `k ≥ 0` with `length + 1 + k ≡ 56 (mod 64)`
  let zeroBytes := ((55 - (msg.length : Int)) % 64).toNat
  msg ++ [0x80] ++ List.replicate zeroBytes 0 ++
    (List.range 8).reverse.map (fun i => BitVec.ofNat 8 (ℓ / 2 ^ (8 * i)))

/-! ## §5.2.1 Parsing the message

A block is sixteen 32-bit words, each formed from four bytes in big-endian
order. -/

/-- Four bytes, most significant first, as a word. -/
def wordBE (b0 b1 b2 b3 : BitVec 8) : Word := b0 ++ b1 ++ b2 ++ b3

/-- Split a list of bytes into 32-bit big-endian words (length must be a multiple of 4). -/
def toWords : List (BitVec 8) → List Word
  | b0 :: b1 :: b2 :: b3 :: rest => wordBE b0 b1 b2 b3 :: toWords rest
  | _ => []

/-- Split a list into consecutive chunks of `n` elements. -/
def chunks {α : Type} (n : Nat) (l : List α) : List (List α) :=
  if h : 0 < n ∧ l ≠ [] then l.take n :: chunks n (l.drop n) else []
termination_by l.length
decreasing_by simp_wf; have := List.length_pos_of_ne_nil h.2; omega

/-- The padded message, parsed into 512-bit blocks of sixteen words. -/
def parse (padded : List (BitVec 8)) : List (List Word) := chunks 16 (toWords padded)

/-! ## §6.2.2 SHA-256 hash computation -/

/-- Step 1: the message schedule `W₀ … W₆₃` for one block `M`. -/
def schedule (M : List Word) : List Word :=
  (List.range 48).foldl
    (fun W t => W ++ [sigma1 W[t + 14]! + W[t + 9]! + sigma0 W[t + 1]! + W[t]!])
    M

/-- The eight working variables `a, b, c, d, e, f, g, h`. -/
structure Vars where
  a : Word
  b : Word
  c : Word
  d : Word
  e : Word
  f : Word
  g : Word
  h : Word
  deriving DecidableEq, Repr

/-- Step 3: one round `t` of the compression function, given `Kₜ` and `Wₜ`. -/
def round (v : Vars) (Kt Wt : Word) : Vars :=
  let T₁ := v.h + SIGMA1 v.e + Ch v.e v.f v.g + Kt + Wt
  let T₂ := SIGMA0 v.a + Maj v.a v.b v.c
  { h := v.g, g := v.f, f := v.e, e := v.d + T₁, d := v.c, c := v.b, b := v.a, a := T₁ + T₂ }

/-- Steps 1-4: process one block, updating the intermediate hash value `H`. -/
def compress (H : List Word) (M : List Word) : List Word :=
  let W := schedule M
  -- Step 2: initialize the working variables with the (i-1)st hash value.
  let v₀ : Vars := ⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩
  -- Step 3: 64 rounds.
  let v := (List.range 64).foldl (fun v t => round v K[t]! W[t]!) v₀
  -- Step 4: compute the i-th intermediate hash value.
  [v.a + H[0]!, v.b + H[1]!, v.c + H[2]!, v.d + H[3]!,
   v.e + H[4]!, v.f + H[5]!, v.g + H[6]!, v.h + H[7]!]

/-- The final hash value, as bytes: `H₀ ‖ H₁ ‖ … ‖ H₇`, each big-endian. -/
def toBytes (H : List Word) : List (BitVec 8) :=
  H.flatMap (fun w => [w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8])

/-- SHA-256 of a message given as a list of bytes. -/
def sha256 (msg : List (BitVec 8)) : List (BitVec 8) :=
  toBytes ((parse (pad msg)).foldl compress H0)

end CC.Spec.SHA256
