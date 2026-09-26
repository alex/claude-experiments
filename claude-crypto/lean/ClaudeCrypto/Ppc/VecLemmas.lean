import ClaudeCrypto.Ppc.Basic
import ClaudeCrypto.Common.MemLemmas

/-! # Lemmas about 128-bit vectors as four 32-bit words (not part of the TCB) -/

namespace CC.Ppc

set_option linter.unusedSimpArgs false

/-- The vector with ISA words `word[0] = a`, …, `word[3] = d` (`a` most significant). -/
def w4 (a b c d : BitVec 32) : BitVec 128 := a ++ b ++ c ++ d

/-- Prove an equation between vectors built from `w4`, `++` and `extractLsb'`, bit by bit. -/
macro "vec_tac" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [w4, word, dword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> (try simp (disch := omega) only [decide_eq_true, Bool.true_and, Bool.and_true,
    BitVec.getLsbD_of_ge, Bool.false_and, Bool.and_false]) <;>
    first | rfl | (congr 1; omega) | omega))

theorem word_w4_0 (a b c d : BitVec 32) : word (w4 a b c d) 0 = a := by vec_tac
theorem word_w4_1 (a b c d : BitVec 32) : word (w4 a b c d) 1 = b := by vec_tac
theorem word_w4_2 (a b c d : BitVec 32) : word (w4 a b c d) 2 = c := by vec_tac
theorem word_w4_3 (a b c d : BitVec 32) : word (w4 a b c d) 3 = d := by vec_tac

theorem w4_word (x : BitVec 128) : w4 (word x 0) (word x 1) (word x 2) (word x 3) = x := by vec_tac

theorem vadduwm_eq (x y : BitVec 128) :
    vadduwm x y = w4 (word x 0 + word y 0) (word x 1 + word y 1) (word x 2 + word y 2)
      (word x 3 + word y 3) := rfl

theorem vadduwm_w4 (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 32) :
    vadduwm (w4 a0 a1 a2 a3) (w4 b0 b1 b2 b3) = w4 (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) := by
  simp only [vadduwm_eq, word_w4_0, word_w4_1, word_w4_2, word_w4_3]

theorem word_vadduwm_0 (x y : BitVec 128) : word (vadduwm x y) 0 = word x 0 + word y 0 := by
  rw [vadduwm_eq, word_w4_0]

theorem vshasigmaw_eq (x : BitVec 128) (st : Bool) (six : Nat) :
    vshasigmaw x st six = w4 (shaSigmaWord st (six.testBit 3) (word x 0))
      (shaSigmaWord st (six.testBit 2) (word x 1)) (shaSigmaWord st (six.testBit 1) (word x 2))
      (shaSigmaWord st (six.testBit 0) (word x 3)) := rfl

theorem word_vshasigmaw_0 (x : BitVec 128) (st : Bool) (six : Nat) :
    word (vshasigmaw x st six) 0 = shaSigmaWord st (six.testBit 3) (word x 0) := by
  rw [vshasigmaw_eq, word_w4_0]

theorem word_xor (x y : BitVec 128) (i : Nat) : word (x ^^^ y) i = word x i ^^^ word y i := by
  simp only [word, BitVec.extractLsb'_xor]

theorem word_vsel_0 (a b c : BitVec 128) :
    word (vsel a b c) 0 = (word a 0 &&& ~~~word c 0) ||| (word b 0 &&& word c 0) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vsel, word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and, Nat.reduceMul, Nat.reduceSub]
  simp only [show 96 + i < 128 by omega, decide_true, Bool.true_and]

set_option maxRecDepth 20000 in
theorem vsldoi_4 (x y : BitVec 128) :
    vsldoi x y 4 = w4 (word x 1) (word x 2) (word x 3) (word y 0) := by
  unfold vsldoi; vec_tac

set_option maxRecDepth 20000 in
theorem vsldoi_8 (x y : BitVec 128) :
    vsldoi x y 8 = w4 (word x 2) (word x 3) (word y 0) (word y 1) := by
  unfold vsldoi; vec_tac

set_option maxRecDepth 20000 in
theorem vsldoi_12 (x y : BitVec 128) :
    vsldoi x y 12 = w4 (word x 3) (word y 0) (word y 1) (word y 2) := by
  unfold vsldoi; vec_tac

theorem vmrghw_eq (x y : BitVec 128) : vmrghw x y = w4 (word x 0) (word y 0) (word x 1) (word y 1) :=
  rfl

set_option maxRecDepth 20000 in
theorem xxpermdi_0 (a b c d e f g h : BitVec 32) :
    xxpermdi (w4 a b c d) (w4 e f g h) 0 = w4 a b e f := by
  unfold xxpermdi
  simp only [Nat.zero_testBit, Bool.false_eq_true, ite_false]
  vec_tac

/-- The value loaded by `lxvw4x`. -/
theorem lxvw4x_eq (m : Mem) (a : Addr) :
    m.readW a 32 ++ m.readW (a + 4) 32 ++ m.readW (a + 8) 32 ++ m.readW (a + 12) 32 =
      w4 (m.readW a 32) (m.readW (a + 4) 32) (m.readW (a + 8) 32) (m.readW (a + 12) 32) := rfl

/-! ## Byte swap with `vperm` -/

/-- Reverse the bytes of a word. -/
def bswap (x : BitVec 32) : BitVec 32 :=
  x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8

/-- The permutation reversing the bytes of each word (ISA bytes
`3,2,1,0, 7,6,5,4, 11,10,9,8, 15,14,13,12`). -/
def bswapVec : BitVec 128 := 0x03020100070605040b0a09080f0e0d0c#128

theorem bswapVec_eq : w4 0x03020100 0x07060504 0x0b0a0908 0x0f0e0d0c = bswapVec := by
  simp only [w4, bswapVec, BitVec.reduceAppend]

set_option maxRecDepth 20000 in
theorem vperm_bswap (a b c d : BitVec 32) :
    vperm (w4 a b c d) (w4 a b c d) bswapVec = w4 (bswap a) (bswap b) (bswap c) (bswap d) := by
  simp only [vperm, bswapVec, byteAt, Nat.reduceMul, Nat.reduceSub, BitVec.reduceExtractLsb',
    BitVec.reduceToNat, Nat.reduceMod]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [w4, bswap, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

/-- A byte-swapped little-endian word is the big-endian word. -/
theorem bswap_readW (m : Mem) (a : Addr) :
    bswap (m.readW a 32) = m a ++ m (a + 1) ++ m (a + 2) ++ m (a + 3) := by
  simp only [bswap, Mem.readW, Mem.read]
  have e2 : a + 1 + 1 = a + 2 := by rw [BitVec.add_assoc]; rfl
  have e3 : a + 2 + 1 = a + 3 := by rw [BitVec.add_assoc]; rfl
  rw [e2, e3]
  generalize m a = b0; generalize m (a + 1) = b1; generalize m (a + 2) = b2; generalize m (a + 3) = b3
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

end CC.Ppc
