import ClaudeCrypto.P384.Final
import ClaudeCrypto.P384.MainSpec
import ClaudeCrypto.P384.Consts

/-!
# Loading the inputs and the constants into the frame
-/

set_option exponentiation.threshold 1000

namespace CC.P384

open CC.Limb CC.Spec.P384

/-- A sequence of blocks, each writing one (distinct) slot with a known value. -/
theorem writes_ok (s0 : State) : ∀ (steps : List (List Instr × Nat × Nat)),
    (steps.map (·.2.1)).Nodup → (∀ st ∈ steps, st.2.1 < nSlots) →
    (∀ st ∈ steps, ∀ q, Inv q → Frm s0 q → RegsExcept [9] s0 q →
      ∃ q', execBlock isa st.1 q = some q' ∧ Eff [st.2.1] q q'.1 ∧ sv q'.1 st.2.1 = st.2.2 ∧
        RegsExcept [9] q q'.1) →
    ∀ q, Inv q → Frm s0 q → RegsExcept [9] s0 q →
    ∃ q', execBlock isa (steps.flatMap (·.1)) q = some q' ∧ Inv q'.1 ∧ Eff (steps.map (·.2.1)) q q'.1 ∧
      (∀ st ∈ steps, sv q'.1 st.2.1 = st.2.2) ∧ RegsExcept [9] q q'.1
  | [], _, _, _, q, hI, _, _ =>
    ⟨(q, []), rfl, hI, Eff.refl q, fun _ h => absurd h (by simp), fun _ _ => rfl⟩
  | st :: rest, hnd, hlt, hst, q, hI, hF, hR => by
    obtain ⟨q1, hq1, hE1, hv1, hR1⟩ := hst st (by simp) q hI hF hR
    have hI1 := hI.frm hE1.frm
    obtain ⟨q2, hq2, hI2, hE2, hv2, hR2⟩ := writes_ok s0 rest (List.nodup_cons.mp hnd).2
      (fun st' h => hlt st' (by simp [h])) (fun st' h => hst st' (by simp [h])) q1.1 hI1
      (hF.trans hE1.frm) ((hR.trans hR1).mono (by simp))
    refine ⟨(q2.1, q1.2 ++ q2.2), by rw [List.flatMap_cons]; exact exec_append hq1 hq2, hI2,
      (hE1.trans hE2).mono (by simp), fun st' h' => ?_, (hR1.trans hR2).mono (by simp)⟩
    rcases List.mem_cons.mp h' with rfl | h'
    · rw [hE2.keep _ (hlt _ (by simp)) (List.nodup_cons.mp hnd).1, hv1]
    · exact hv2 st' h'

theorem Within.offset {rs : List Region} {a : Addr} {len : Nat} (h : Within rs a len) (k l : Nat)
    (hkl : k + l ≤ len) : Within rs (a + BitVec.ofNat 64 k) l := by
  obtain ⟨r, hr, hlen, hc⟩ := h
  refine ⟨r, hr, hlen, ?_⟩
  unfold Region.Contains at *
  rw [show a + BitVec.ofNat 64 k - r.base = (a - r.base) + BitVec.ofNat 64 k by abel,
    BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- The frame slots after `setup`. -/
structure Loaded (s q : State) : Prop where
  qx : sv q sQx = bytesToNat (inBytes s.mem (s.r 5) 48)
  qy : sv q sQy = bytesToNat (inBytes s.mem (s.r 5 + 48#64) 48)
  e : sv q sE = bytesToNat (inBytes s.mem (s.r 4) 48)
  r : sv q sR = bytesToNat (inBytes s.mem (s.r 0) 48)
  s : sv q sS = bytesToNat (inBytes s.mem (s.r 0 + 48#64) 48)
  gx : sv q sG = Gx * R % p
  gy : sv q (sG + 1) = Gy * R % p
  g1 : sv q (sG + 2) = R % p
  q1 : sv q (sQ + 2) = R % p
  r2p : sv q sR2P = R * R % p
  b : sv q sB = b * R % p
  r2n : sv q sR2N = R * R % n
  oneN : sv q sOneN = R % n
  exp : sv q sExp = n - 2
  nm : sv q sNm = n * R % p

/-- `q` differs from `s` only in the frame and the registers. -/
structure Out (s q : State) : Prop where
  r14 : q.r 14 = s.r 14
  rd : q.rd = s.rd
  wr : q.wr = s.wr
  labels : q.labels = s.labels
  agree : Mem.Agree s.mem q.mem ⟨s.r 14, frameSize⟩

theorem Out.frm {s q u : State} (h : Out s q) (hf : Frm q u) : Out s u :=
  ⟨hf.r14.trans h.r14, hf.rd.trans h.rd, hf.wr.trans h.wr, hf.labels.trans h.labels,
    h.agree.trans (by have := hf.agree; rwa [h.r14] at this)⟩

theorem inBytes_congr_frame {m m' : Mem} {fr a : Addr} {len : Nat} (hag : Mem.Agree m m' ⟨fr, frameSize⟩)
    (hsep : Mem.Sep fr frameSize a len) : inBytes m' a len = inBytes m a len := by
  unfold inBytes
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  exact hag.apply _ (hsep.mono 0 j frameSize 1 (by omega) (by omega) (by decide) (by decide) |>.symm |> fun h => by
    simpa using h.symm)

theorem setup_ok (s : State) (h : MainPre s) :
    WP isa (.block setup) s (fun q => Inv q ∧ Out s q ∧ Loaded s q) := by
  set s1 := s.set 13 (s.labels constLabel + BitVec.ofNat 64 0) with hs1
  have e13 : s1.r 13 = s.labels constLabel := by simp [hs1, State.set]
  have er : ∀ v, v ≠ 13 → s1.r v = s.r v := fun v hv => by simp [hs1, State.set, Function.update_of_ne hv]
  have hI1 : Inv s1 := by
    refine ⟨?_, ?_, ?_, constVals_of_table s1 (by rw [e13]; exact h.tab)⟩
    · rw [er 14 (by decide)]; exact h.fr
    · rw [e13]; exact h.cs
    · rw [e13, er 14 (by decide)]; exact h.sepC
  have hO1 : Out s s1 := ⟨er 14 (by decide), rfl, rfl, rfl, Mem.Agree.refl _ _⟩
  -- inputs, as seen from any state that differs from `s1` only in the frame and `r9`
  have inp : ∀ q, Frm s1 q → RegsExcept [9] s1 q → ∀ (b : Var) (off len : Nat), b ≠ 9 → b ≠ 13 →
      Mem.Sep (s.r 14) frameSize (s.r b + BitVec.ofNat 64 off) len →
      inBytes q.mem (q.r b + BitVec.ofNat 64 off) len = inBytes s.mem (s.r b + BitVec.ofNat 64 off) len := by
    intro q hF hR b off len hb9 hb13 hsep
    rw [hR b (by simpa using hb9), er b hb13]
    have := hF.agree; rw [er 14 (by decide)] at this
    exact inBytes_congr_frame this hsep
  have z0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => by simp
  let steps : List (List Instr × Nat × Nat) :=
    [ (loadBE sQx 5 0, sQx, bytesToNat (inBytes s.mem (s.r 5) 48)),
      (loadBE sQy 5 48, sQy, bytesToNat (inBytes s.mem (s.r 5 + 48#64) 48)),
      (loadBE sE 4 0, sE, bytesToNat (inBytes s.mem (s.r 4) 48)),
      (loadBE sR 0 0, sR, bytesToNat (inBytes s.mem (s.r 0) 48)),
      (loadBE sS 0 48, sS, bytesToNat (inBytes s.mem (s.r 0 + 48#64) 48)),
      (copyConst sG cGx, sG, Gx * R % p), (copyConst (sG + 1) cGy, sG + 1, Gy * R % p),
      (copyConst (sG + 2) cOneP, sG + 2, R % p), (copyConst (sQ + 2) cOneP, sQ + 2, R % p),
      (copyConst sR2P cR2P, sR2P, R * R % p), (copyConst sB cB, sB, b * R % p),
      (copyConst sR2N cR2N, sR2N, R * R % n), (copyConst sOneN cOneN, sOneN, R % n),
      (copyConst sExp cNm2, sExp, n - 2), (copyConst sNm cNm, sNm, n * R % p) ]
  have hsetup : setup = [.lea 13 constLabel 0] ++ steps.flatMap (·.1) := rfl
  have hstep : ∀ st ∈ steps, ∀ q, Inv q → Frm s1 q → RegsExcept [9] s1 q →
      ∃ q', execBlock isa st.1 q = some q' ∧ Eff [st.2.1] q q'.1 ∧ sv q'.1 st.2.1 = st.2.2 ∧
        RegsExcept [9] q q'.1 := by
    intro st hst q hI hF hR
    have ld : ∀ (d : Nat) (b : Var) (off len : Nat), off ≤ 48 → d < nSlots → b ≠ 9 → b ≠ 13 → b ≠ 14 →
        off + 48 ≤ len →
        Within (s.rd ++ s.wr) (s.r b) len → Mem.Sep (s.r 14) frameSize (s.r b) len →
        ∃ q', execBlock isa (loadBE d b off) q = some q' ∧ Eff [d] q q'.1 ∧
          sv q'.1 d = bytesToNat (inBytes s.mem (s.r b + BitVec.ofNat 64 off) 48) ∧ RegsExcept [9] q q'.1 := by
      intro d b off len hoff hd hb9 hb13 hb14 hlen hW hS
      have hrb : q.r b = s.r b := by rw [hR b (by simpa using hb9), er b hb13]
      have h14 : q.r 14 = s.r 14 := by rw [hF.r14, er 14 (by decide)]
      have hS' : Mem.Sep (s.r 14) frameSize (s.r b + BitVec.ofNat 64 off) 48 := by
        have := hS.mono 0 off frameSize 48 (by omega) hlen (by decide) (by decide); simpa using this
      obtain ⟨q', hq', hE, hv, hr, -⟩ := loadBE_exec d b off q hI hd hb9 hb14 (by omega)
        (by rw [hF.rd, hF.wr, hrb]; exact hW.offset off 48 hlen)
        (by rw [hrb, h14]; exact hS')
      refine ⟨q', hq', hE, ?_, hr⟩
      rw [hv, inp q hF hR b off 48 hb9 hb13 hS']
    have cc : ∀ (d c v : Nat), d < nSlots → c + 48 ≤ constSize → cval q c = v →
        ∃ q', execBlock isa (copyConst d c) q = some q' ∧ Eff [d] q q'.1 ∧ sv q'.1 d = v ∧
          RegsExcept [9] q q'.1 := by
      intro d c v hd hc hv
      obtain ⟨q', hq', hE, hsv, hr, -⟩ := copyConst_exec d c q hI hd hc
      exact ⟨q', hq', hE, hsv.trans hv, hr⟩
    have V := hI.vals
    simp only [steps, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have := ld sQx 5 0 96 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.inPk h.sepPk
      rwa [z0] at this
    · exact ld sQy 5 48 96 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.inPk h.sepPk
    · have := ld sE 4 0 48 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.inDg h.sepDg
      rwa [z0] at this
    · have := ld sR 0 0 96 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.inSg h.sepSg
      rwa [z0] at this
    · exact ld sS 0 48 96 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.inSg h.sepSg
    · exact cc _ _ _ (by decide) (by decide) V.hgx
    · exact cc _ _ _ (by decide) (by decide) V.hgy
    · exact cc _ _ _ (by decide) (by decide) V.honeP
    · exact cc _ _ _ (by decide) (by decide) V.honeP
    · exact cc _ _ _ (by decide) (by decide) V.hr2p
    · exact cc _ _ _ (by decide) (by decide) V.hb
    · exact cc _ _ _ (by decide) (by decide) V.hr2n
    · exact cc _ _ _ (by decide) (by decide) V.honeN
    · exact cc _ _ _ (by decide) (by decide) V.hnm2
    · exact cc _ _ _ (by decide) (by decide) V.hnm
  obtain ⟨q, hq, hIq, hEq, hvq, -⟩ := writes_ok s1 steps (by simp only [steps, List.map_cons, List.map_nil]; decide)
    (by simp only [steps, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; decide) hstep s1 hI1 (Frm.refl _)
    (fun _ _ => rfl)
  rw [hsetup]
  refine WP.block_intro (q.1, [] ++ q.2) (exec_append (q₁ := (s1, [])) rfl hq) ?_
  have v := fun st (h : st ∈ steps) => hvq st h
  simp only [steps, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at v
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩ := v
  exact ⟨hIq, hO1.frm hEq.frm, ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩⟩

end CC.P384
