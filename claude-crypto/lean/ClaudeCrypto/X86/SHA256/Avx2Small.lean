import ClaudeCrypto.X86.SHA256.Avx2
import ClaudeCrypto.X86.Sym

/-! # AVX2 SHA-256: parity test and pointer updates -/

namespace CC.X86.SHA256Avx2

open BitVec CC.X86

theorem parity_exec (s : State) :
    ∃ q, execBlock isa parity s = some q ∧ q.1.zf = some ((s.gpr.rdx.setWidth 32 &&& 1#32) == 0#32) ∧
      q.1.gpr = s.gpr ∧ q.1.vec = s.vec ∧ q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧
      q.1.labels = s.labels := by
  simp only [parity]
  x86_sym
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem parity_bit (x : Nat) (hx : x < 2 ^ 64) :
    (((BitVec.ofNat 64 x).setWidth 32 &&& 1#32) == 0#32) = decide (x % 2 = 0) := by
  have h : ((BitVec.ofNat 64 x).setWidth 32 &&& 1#32) = BitVec.ofNat 32 (x % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.and_one_is_mod]
    omega
  rw [h]
  by_cases h2 : x % 2 = 0
  · simp [h2]
  · have : x % 2 = 1 := by omega
    simp [this]

theorem tail1_exec (s : State) :
    ∃ q, execBlock isa [.alu .add .q .rsi (.imm 64), .alu .sub .q .rdx (.imm 1)] s = some q ∧
      q.1.gpr = { s.gpr with rsi := s.gpr.rsi + 64#64, rdx := s.gpr.rdx - 1#64 } ∧
      q.1.zf = some (s.gpr.rdx - 1#64 == 0#64) ∧
      q.1.vec = s.vec ∧ q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  x86_sym
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tail2_exec (s : State) :
    ∃ q, execBlock isa [.alu .add .q .rsi (.imm 128), .alu .sub .q .rdx (.imm 2)] s = some q ∧
      q.1.gpr = { s.gpr with rsi := s.gpr.rsi + 128#64, rdx := s.gpr.rdx - 2#64 } ∧
      q.1.zf = some (s.gpr.rdx - 2#64 == 0#64) ∧
      q.1.vec = s.vec ∧ q.1.mem = s.mem ∧ q.1.rd = s.rd ∧ q.1.wr = s.wr ∧ q.1.labels = s.labels := by
  x86_sym
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end CC.X86.SHA256Avx2
