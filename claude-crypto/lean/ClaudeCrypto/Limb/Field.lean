import ClaudeCrypto.Limb.MontFinal

/-! # Montgomery multiplication: the complete routine -/

namespace CC.Limb

/-- `D := A · B · 2^-384 mod N`, for 6-limb operands at `r14 + offA`, `r14 + offB`, result at
`r14 + offD`; the modulus `N` at `r13 + offN` and `-N⁻¹ mod 2^64` at `r13 + offMp`.
All other registers except `r13`, `r14` are clobbered. -/
def montMul (offA offB offD offN offMp : Nat) : Code Instr Cond :=
  .seq (.block (montInit ++ montRounds offA offB offN offMp)) (montFinal offN offD)

theorem lsum_rowX (s : State) (base : Var) (off : Nat) :
    lsum (rowX s base (fun j => off + 8 * j)) 6 = mval s.mem (s.r base + BitVec.ofNat 64 off) 6 := by
  unfold mval; apply lsum_congr; intro k _; unfold rowX mlimb; rw [addr_add_ofNat']

theorem montMul_ok (offA offB offD offN offMp : Nat) (s : State)
    (hoffD : offD + 48 < 2 ^ 63) (hoffN : offN + 48 < 2 ^ 63)
    (hA : mval s.mem (s.r 14 + BitVec.ofNat 64 offA) 6 < mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6)
    (hmp : ((s.mem.readW (s.r 13 + BitVec.ofNat 64 offMp) 64).toNat *
      mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6 + 1) % 2 ^ 64 = 0)
    (pA : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.r 14 + BitVec.ofNat 64 (offA + 8 * k)) 8)
    (pB : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.r 14 + BitVec.ofNat 64 (offB + 8 * k)) 8)
    (pN : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8)
    (pM : InRegions (s.rd ++ s.wr) (s.r 13 + BitVec.ofNat 64 offMp) 8)
    (pD : ∀ k < 6, InRegions s.wr (s.r 14 + BitVec.ofNat 64 (offD + 8 * k)) 8)
    (hsep : ∀ k < 6, Mem.Sep (s.r 14 + BitVec.ofNat 64 offD) 48 (s.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8) :
    WP isa (montMul offA offB offD offN offMp) s (fun q =>
      mval q.mem (s.r 14 + BitVec.ofNat 64 offD) 6 < mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6 ∧
      (2 ^ 384 * mval q.mem (s.r 14 + BitVec.ofNat 64 offD) 6) % mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6 =
        (mval s.mem (s.r 14 + BitVec.ofNat 64 offA) 6 * mval s.mem (s.r 14 + BitVec.ofNat 64 offB) 6) %
          mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6 ∧
      Mem.Agree s.mem q.mem ⟨s.r 14 + BitVec.ofNat 64 offD, 48⟩ ∧ q.r 13 = s.r 13 ∧ q.r 14 = s.r 14 ∧
      q.rd = s.rd ∧ q.wr = s.wr ∧ q.labels = s.labels) := by
  unfold montMul
  apply WP.seq
  have eA := lsum_rowX s 14 offA
  have eN := lsum_rowX s 13 offN
  refine WP.mono (montRounds_ok offA offB offN offMp s (by unfold opA opN; rw [eA, eN]; exact hA)
    (by unfold opMp opN; rw [eN]; exact hmp) pA pB pN pM) ?_
  intro s1 h1
  have hdA : dAddr offD s1 = s.r 14 + BitVec.ofNat 64 offD := by unfold dAddr; rw [h1.r14]
  have hnA : nAddr offN s1 = s.r 13 + BitVec.ofNat 64 offN := by unfold nAddr; rw [h1.r13]
  have hNv : mval s1.mem (nAddr offN s1) 6 = opN offN s := by
    rw [hnA, h1.mem, opN, eN]
  refine WP.mono (montFinal_ok offN offD s1 hoffD hoffN
    (fun k hk => by rw [h1.rd, h1.wr, h1.r13]; exact pN k hk)
    (fun k hk => by rw [h1.wr, h1.r14]; exact pD k hk)
    (fun k hk => by rw [hdA, h1.r13]; exact hsep k hk) h1.z (by rw [hNv]; exact h1.lt)) ?_
  rintro q ⟨hv, hag, h13, h14, hrd, hwr, hl⟩
  rw [hNv, hdA] at hv
  rw [hdA, h1.mem] at hag
  refine ⟨?_, ?_, hag, h13.trans h1.r13, h14.trans h1.r14, hrd.trans h1.rd, hwr.trans h1.wr,
    hl.trans h1.labels⟩
  · have hlt : acc s1 6 7 < 2 * lsum (rowX s 13 (fun j => offN + 8 * j)) 6 := h1.lt
    rw [hv, ← eN]
    split_ifs with h
    · exact h
    · have : opN offN s = lsum (rowX s 13 fun j => offN + 8 * j) 6 := rfl
      omega
  · obtain ⟨Q, hQ⟩ := h1.eq
    rw [hv, ← eN, ← eA, show mval s.mem (s.r 14 + BitVec.ofNat 64 offB) 6 = lsum (digB offB s) 6 from by
      rw [← lsum_rowX]; rfl]
    unfold opA opN at hQ
    have hlt := h1.lt; unfold opN at hlt
    set N := lsum (rowX s 13 fun j => offN + 8 * j) 6
    set T := acc s1 6 7
    have hmod : (2 ^ 384 * T) % N = (lsum (rowX s 14 fun j => offA + 8 * j) 6 * lsum (digB offB s) 6) % N := by
      rw [show 64 * 6 = 384 by rfl] at hQ
      rw [hQ, Nat.add_mul_mod_self_right]
    split_ifs with h
    · exact hmod
    · push_neg at h
      rw [show opN offN s = N from rfl] at h ⊢
      rw [Nat.mul_sub, show 2 ^ 384 * N = N * 2 ^ 384 by ring,
        Nat.sub_mul_mod (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ h), hmod]

end CC.Limb
