import ClaudeCrypto.Limb.AddSub

/-!
# Field programs

A field program is a list of `mul`/`add`/`sub` operations on 48-byte slots of
the frame (`r14 + base + 48·i`), all modulo the same `N` (given by its offsets
in the constants table at `r13`).  `FProg.run` is its meaning on the decoded
values in `ZMod N` (a slot holding `x < N` decodes to `x · 2^-384`), and
`fprog_ok` shows that the compiled code computes it.
-/

namespace CC.Limb

inductive FOp where
  | mul (d a b : Nat)
  | add (d a b : Nat)
  | sub (d a b : Nat)
  deriving DecidableEq, Repr

namespace FOp

def dst : FOp → Nat
  | mul d _ _ | add d _ _ | sub d _ _ => d

def srcs : FOp → List Nat
  | mul _ a b | add _ a b | sub _ a b => [a, b]

/-- The sources that must be reduced (`montMul` only needs its first operand `< N`). -/
def rsrcs : FOp → List Nat
  | mul _ a _ => [a]
  | add _ a b | sub _ a b => [a, b]

/-- Frame offset of slot `i`. -/
def off (base i : Nat) : Nat := base + 48 * i

def code (offN offMp base : Nat) : FOp → Code Instr Cond
  | mul d a b => montMul (off base a) (off base b) (off base d) offN offMp
  | add d a b => addMod (off base a) (off base b) (off base d) offN
  | sub d a b => subMod (off base a) (off base b) (off base d) offN

/-- Meaning on decoded values. -/
def run {N : Nat} (o : FOp) (v : Nat → ZMod N) : Nat → ZMod N :=
  match o with
  | mul d a b => Function.update v d (v a * v b)
  | add d a b => Function.update v d (v a + v b)
  | sub d a b => Function.update v d (v a - v b)

end FOp

def FProg := List FOp

def FProg.code (offN offMp base : Nat) : List FOp → Code Instr Cond
  | [] => .block []
  | o :: os => .seq (o.code offN offMp base) (FProg.code offN offMp base os)

def FProg.run {N : Nat} : List FOp → (Nat → ZMod N) → (Nat → ZMod N)
  | [], v => v
  | o :: os, v => FProg.run os (o.run v)

/-- Every slot that must be reduced has been initialized (is in `init`) or written before;
all slots `< K`. -/
def FProg.wf (K : Nat) : List FOp → List Nat → Bool
  | [], _ => true
  | o :: os, init => (o.rsrcs.all fun i => init.contains i) && decide (o.dst < K) &&
      (o.srcs.all fun i => decide (i < K)) && FProg.wf K os (o.dst :: init)

/-! ## Decoding Montgomery representations -/

/-- The value represented by `x` (Montgomery form with `R = 2^384`). -/
def decode (N x : Nat) : ZMod N := (x : ZMod N) * ((2 ^ 384 : ℕ) : ZMod N)⁻¹

theorem decode_mul (N A B D : Nat) (hc : Nat.Coprime (2 ^ 384) N)
    (hD : (2 ^ 384 * D) % N = (A * B) % N) : decode N D = decode N A * decode N B := by
  have h : ((2 ^ 384 : ℕ) : ZMod N) * (D : ZMod N) = (A : ZMod N) * (B : ZMod N) := by
    have := congrArg (fun x : ℕ => (x : ZMod N)) hD
    simpa [ZMod.natCast_mod, Nat.cast_mul] using this
  have hu := ZMod.coe_mul_inv_eq_one _ hc
  unfold decode
  calc (D : ZMod N) * ((2 ^ 384 : ℕ) : ZMod N)⁻¹
      = (D : ZMod N) * ((2 ^ 384 : ℕ) : ZMod N)⁻¹ * (((2 ^ 384 : ℕ) : ZMod N) * ((2 ^ 384 : ℕ) : ZMod N)⁻¹) := by
        rw [hu, mul_one]
    _ = (((2 ^ 384 : ℕ) : ZMod N) * D) * ((2 ^ 384 : ℕ) : ZMod N)⁻¹ * ((2 ^ 384 : ℕ) : ZMod N)⁻¹ := by ring
    _ = _ := by rw [h]; ring

theorem decode_add (N A B D : Nat) (hD : D = (A + B) % N) : decode N D = decode N A + decode N B := by
  unfold decode; rw [hD, ZMod.natCast_mod, Nat.cast_add]; ring

theorem decode_sub (N A B D : Nat) (hB : B ≤ N) (hD : D = (A + (N - B)) % N) :
    decode N D = decode N A - decode N B := by
  unfold decode; rw [hD, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub hB, ZMod.natCast_self]; ring

/-! ## The memory layout -/

section
variable (offN offMp base K N : Nat)

def slotAddr (s : State) (i : Nat) : Addr := s.r 14 + BitVec.ofNat 64 (FOp.off base i)
def slotVal (s : State) (i : Nat) : Nat := mval s.mem (slotAddr base s i) 6
def nVal (s : State) : Nat := mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6
def mpVal (s : State) : Nat := (s.mem.readW (s.r 13 + BitVec.ofNat 64 offMp) 64).toNat

structure Layout (s : State) : Prop where
  nv : nVal offN s = N
  hoffs : base + 48 * K < 2 ^ 62
  hoffN : offN + 48 < 2 ^ 63
  pS : ∀ i < K, ∀ k < 6, InRegions s.wr (s.r 14 + BitVec.ofNat 64 (FOp.off base i + 8 * k)) 8
  pN : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8
  pM : InRegions (s.rd ++ s.wr) (s.r 13 + BitVec.ofNat 64 offMp) 8
  sepN : ∀ i < K, ∀ k < 6, Mem.Sep (slotAddr base s i) 48 (s.r 13 + BitVec.ofNat 64 (offN + 8 * k)) 8
  sepM : ∀ i < K, Mem.Sep (slotAddr base s i) 48 (s.r 13 + BitVec.ofNat 64 offMp) 8
  hmp : (mpVal offMp s * N + 1) % 2 ^ 64 = 0
  cop : Nat.Coprime (2 ^ 384) N
end

theorem slot_sep (base K : Nat) (s : State) (hK : base + 48 * K < 2 ^ 62) (i d : Nat) (hi : i < K) (hd : d < K)
    (hne : i ≠ d) (k : Nat) (hk : k < 6) :
    Mem.Sep (slotAddr base s d) 48 (slotAddr base s i + BitVec.ofNat 64 (8 * k)) 8 := by
  unfold slotAddr FOp.off
  rw [addr_add_ofNat']
  apply sep_offsets _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · right; nlinarith
  · left; nlinarith

/-- Writing slot `d` preserves the layout, the modulus and all other slots. -/
theorem Layout.preserve {offN offMp base K N : Nat} {s q : State} (hl : Layout offN offMp base K N s)
    (d : Nat) (hd : d < K) (h13 : q.r 13 = s.r 13) (h14 : q.r 14 = s.r 14) (hrd : q.rd = s.rd)
    (hwr : q.wr = s.wr) (hag : Mem.Agree s.mem q.mem ⟨slotAddr base s d, 48⟩) :
    Layout offN offMp base K N q ∧ nVal offN q = nVal offN s ∧ mpVal offMp q = mpVal offMp s ∧
      ∀ i < K, i ≠ d → slotVal base q i = slotVal base s i := by
  have sa : ∀ i, slotAddr base q i = slotAddr base s i := fun i => by unfold slotAddr; rw [h14]
  have hN : nVal offN q = nVal offN s := by
    unfold nVal mval; apply lsum_congr; intro k hk
    unfold mlimb; rw [h13, addr_add_ofNat', hag.readW _ _ (by
      have := hl.sepN d hd k hk; exact this)]
  have hM : mpVal offMp q = mpVal offMp s := by
    unfold mpVal; rw [h13, hag.readW _ _ (hl.sepM d hd)]
  refine ⟨⟨hN.trans hl.nv, hl.hoffs, hl.hoffN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hN, hM, fun i hi hne => ?_⟩
  · rw [hwr, h14]; exact hl.pS
  · rw [hrd, hwr, h13]; exact hl.pN
  · rw [hrd, hwr, h13]; exact hl.pM
  · intro i hi k hk; rw [sa, h13]; exact hl.sepN i hi k hk
  · intro i hi; rw [sa, h13]; exact hl.sepM i hi
  · rw [hM]; exact hl.hmp
  · exact hl.cop
  · unfold slotVal mval; rw [sa]; apply lsum_congr; intro k hk
    unfold mlimb; rw [hag.readW _ _ (slot_sep base K s hl.hoffs i d hi hd hne k hk)]

theorem mval_slot (base : Nat) (s : State) (i : Nat) :
    mval s.mem (s.r 14 + BitVec.ofNat 64 (FOp.off base i)) 6 = slotVal base s i := rfl

/-- The post-state of one operation. -/
structure OpPost (offN offMp base K N : Nat) (o : FOp) (s q : State) : Prop where
  layout : Layout offN offMp base K N q
  red : slotVal base q o.dst < N
  val : decode N (slotVal base q o.dst) =
    o.run (fun i => decode N (slotVal base s i)) o.dst
  others : ∀ i < K, i ≠ o.dst → slotVal base q i = slotVal base s i
  agree : Mem.Agree s.mem q.mem ⟨slotAddr base s o.dst, 48⟩
  r13 : q.r 13 = s.r 13
  r14 : q.r 14 = s.r 14
  rd : q.rd = s.rd
  wr : q.wr = s.wr
  labels : q.labels = s.labels

theorem op_ok (offN offMp base K N : Nat) (o : FOp) (s : State) (hl : Layout offN offMp base K N s)
    (hd : o.dst < K) (hk : ∀ i ∈ o.srcs, i < K) (hs : ∀ i ∈ o.rsrcs, slotVal base s i < N) :
    WP isa (o.code offN offMp base) s (OpPost offN offMp base K N o s) := by
  have hpre : ∀ a b d, a < K → b < K → d < K → OpPre (FOp.off base a) (FOp.off base b) (FOp.off base d) offN s :=
    fun a b d ha hb hd => ⟨by unfold FOp.off; nlinarith [hl.hoffs], hl.hoffN,
      fun k hk => (inRegions_append _ _ _ _).mpr (Or.inr (hl.pS a ha k hk)),
      fun k hk => (inRegions_append _ _ _ _).mpr (Or.inr (hl.pS b hb k hk)),
      hl.pN, hl.pS d hd, hl.sepN d hd⟩
  have hNv : mval s.mem (s.r 13 + BitVec.ofNat 64 offN) 6 = N := hl.nv
  have fin : ∀ q, q.r 13 = s.r 13 → q.r 14 = s.r 14 → q.rd = s.rd → q.wr = s.wr →
      Mem.Agree s.mem q.mem ⟨slotAddr base s o.dst, 48⟩ →
      Layout offN offMp base K N q ∧ ∀ i < K, i ≠ o.dst → slotVal base q i = slotVal base s i :=
    fun q a b c d e => by
      obtain ⟨h1, -, -, h4⟩ := hl.preserve o.dst hd a b c d e
      exact ⟨h1, h4⟩
  have hpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · have := hl.cop; rw [h] at this; norm_num at this
    · exact h
  cases o with
  | mul d a b =>
    have ha := hk a (by simp [FOp.srcs]); have hA := hs a (by simp [FOp.rsrcs])
    have hb := hk b (by simp [FOp.srcs])
    have h := hpre a b d ha hb hd
    refine WP.mono (montMul_ok _ _ _ offN offMp s h.hoffD h.hoffN (by rw [hNv]; exact hA)
      (by rw [hNv]; exact hl.hmp) h.pA h.pB h.pN hl.pM h.pD h.sep) ?_
    rintro q ⟨hlt, hmod, hag, h13, h14, hrd, hwr, hl'⟩
    rw [hNv] at hlt hmod
    obtain ⟨L, ho⟩ := fin q h13 h14 hrd hwr hag
    have e1 : slotVal base q d = mval q.mem (s.r 14 + BitVec.ofNat 64 (FOp.off base d)) 6 := by
      unfold slotVal slotAddr; rw [h14]
    refine ⟨L, ?_, ?_, ho, hag, h13, h14, hrd, hwr, hl'⟩
    · show slotVal base q d < N
      rw [e1]; exact hlt
    · simp only [FOp.run, FOp.dst, Function.update_self]
      rw [e1]
      exact decode_mul _ _ _ _ hl.cop hmod
  | add d a b =>
    have ha := hk a (by simp [FOp.srcs]); have hA := hs a (by simp [FOp.rsrcs])
    have hb := hk b (by simp [FOp.srcs]); have hB := hs b (by simp [FOp.rsrcs])
    have h := hpre a b d ha hb hd
    refine WP.mono (addMod_ok _ _ _ offN s h (by rw [hNv]; exact hA) (by rw [hNv]; exact hB)) ?_
    rintro q ⟨hv, hag, h13, h14, hrd, hwr, hl'⟩
    rw [hNv] at hv
    obtain ⟨L, ho⟩ := fin q h13 h14 hrd hwr hag
    have e1 : slotVal base q d = mval q.mem (s.r 14 + BitVec.ofNat 64 (FOp.off base d)) 6 := by
      unfold slotVal slotAddr; rw [h14]
    refine ⟨L, ?_, ?_, ho, hag, h13, h14, hrd, hwr, hl'⟩
    · show slotVal base q d < N
      rw [e1, hv]; exact Nat.mod_lt _ hpos
    · simp only [FOp.run, FOp.dst, Function.update_self]
      rw [e1]
      exact decode_add _ _ _ _ hv
  | sub d a b =>
    have ha := hk a (by simp [FOp.srcs]); have hA := hs a (by simp [FOp.rsrcs])
    have hb := hk b (by simp [FOp.srcs]); have hB := hs b (by simp [FOp.rsrcs])
    have h := hpre a b d ha hb hd
    refine WP.mono (subMod_ok _ _ _ offN s h (by rw [hNv]; exact hA) (by rw [hNv]; exact hB)) ?_
    rintro q ⟨hv, hag, h13, h14, hrd, hwr, hl'⟩
    rw [hNv] at hv
    obtain ⟨L, ho⟩ := fin q h13 h14 hrd hwr hag
    have e1 : slotVal base q d = mval q.mem (s.r 14 + BitVec.ofNat 64 (FOp.off base d)) 6 := by
      unfold slotVal slotAddr; rw [h14]
    refine ⟨L, ?_, ?_, ho, hag, h13, h14, hrd, hwr, hl'⟩
    · show slotVal base q d < N
      rw [e1, hv]; exact Nat.mod_lt _ hpos
    · simp only [FOp.run, FOp.dst, Function.update_self]
      rw [e1]
      exact decode_sub _ _ _ _ (le_of_lt hB) hv

/-- Slots written by a program. -/
def FProg.writes : List FOp → List Nat
  | [] => []
  | o :: os => o.dst :: FProg.writes os

theorem FOp.run_congr {N : Nat} (o : FOp) (K : Nat) (hs : ∀ i ∈ o.srcs, i < K) (v w : Nat → ZMod N)
    (h : ∀ i < K, v i = w i) : ∀ i < K, o.run v i = o.run w i := by
  intro i hi
  cases o with
  | mul d a b =>
    simp only [FOp.run]
    by_cases e : i = d
    · subst e; simp only [Function.update_self]
      rw [h a (hs a (by simp [FOp.srcs])), h b (hs b (by simp [FOp.srcs]))]
    · simp only [Function.update_of_ne e]; exact h i hi
  | add d a b =>
    simp only [FOp.run]
    by_cases e : i = d
    · subst e; simp only [Function.update_self]
      rw [h a (hs a (by simp [FOp.srcs])), h b (hs b (by simp [FOp.srcs]))]
    · simp only [Function.update_of_ne e]; exact h i hi
  | sub d a b =>
    simp only [FOp.run]
    by_cases e : i = d
    · subst e; simp only [Function.update_self]
      rw [h a (hs a (by simp [FOp.srcs])), h b (hs b (by simp [FOp.srcs]))]
    · simp only [Function.update_of_ne e]; exact h i hi

theorem FProg.wf_cons {K : Nat} {o : FOp} {os : List FOp} {init : List Nat} (h : FProg.wf K (o :: os) init = true) :
    (∀ i ∈ o.rsrcs, i ∈ init) ∧ o.dst < K ∧ (∀ i ∈ o.srcs, i < K) ∧ FProg.wf K os (o.dst :: init) = true := by
  simp only [FProg.wf, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem FProg.run_congr {N : Nat} (K : Nat) : ∀ (ops : List FOp) (init : List Nat), FProg.wf K ops init = true →
    ∀ (v w : Nat → ZMod N), (∀ i < K, v i = w i) → ∀ i < K, FProg.run ops v i = FProg.run ops w i
  | [], _, _, v, w, h => h
  | o :: os, init, hwf, v, w, h => by
    obtain ⟨-, -, h3, h4⟩ := FProg.wf_cons hwf
    exact FProg.run_congr K os _ h4 _ _ (o.run_congr K h3 v w h)

theorem agree_slot_area (base K : Nat) (s : State) (hK : base + 48 * K < 2 ^ 62) (d : Nat) (hd : d < K)
    {m m' : Mem} (h : Mem.Agree m m' ⟨slotAddr base s d, 48⟩) :
    Mem.Agree m m' ⟨s.r 14 + BitVec.ofNat 64 base, 48 * K⟩ := by
  intro a ha
  apply h a
  intro hc
  apply ha
  unfold Region.Contains at *
  simp only at *
  unfold slotAddr FOp.off at hc
  rw [show a - (s.r 14 + BitVec.ofNat 64 (base + 48 * d)) =
    (a - (s.r 14 + BitVec.ofNat 64 base)) - BitVec.ofNat 64 (48 * d) by
      rw [← addr_add_ofNat']; abel] at hc
  generalize a - (s.r 14 + BitVec.ofNat 64 base) = x at *
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 48 * d) (by omega)] at hc
  have := x.isLt
  have : 48 * d + 48 ≤ 48 * K := by omega
  rcases Nat.lt_or_ge x.toNat (48 * d) with hx | hx
  · rw [show 2 ^ 64 - 48 * d + x.toNat = (2 ^ 64 - 48 * d + x.toNat) by rfl,
      Nat.mod_eq_of_lt (by omega)] at hc
    omega
  · rw [show 2 ^ 64 - 48 * d + x.toNat = (x.toNat - 48 * d) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)] at hc
    omega

/-- The post-state of a field program. -/
structure ProgPost (offN offMp base K N : Nat) (ops : List FOp) (init : List Nat) (s q : State) : Prop where
  layout : Layout offN offMp base K N q
  red : ∀ i ∈ init ++ FProg.writes ops, slotVal base q i < N
  vals : ∀ i < K, decode N (slotVal base q i) =
    FProg.run ops (fun i => decode N (slotVal base s i)) i
  others : ∀ i < K, i ∉ FProg.writes ops → slotVal base q i = slotVal base s i
  agree : Mem.Agree s.mem q.mem ⟨s.r 14 + BitVec.ofNat 64 base, 48 * K⟩
  r13 : q.r 13 = s.r 13
  r14 : q.r 14 = s.r 14
  rd : q.rd = s.rd
  wr : q.wr = s.wr
  labels : q.labels = s.labels

theorem prog_ok (offN offMp base K N : Nat) : ∀ (ops : List FOp) (init : List Nat) (s : State),
    FProg.wf K ops init = true → Layout offN offMp base K N s →
    (∀ i ∈ init, i < K ∧ slotVal base s i < N) →
    WP isa (FProg.code offN offMp base ops) s (ProgPost offN offMp base K N ops init s)
  | [], init, s, _, hl, hi => WP.block_nil ⟨hl, fun i h => (hi i (by simpa [FProg.writes] using h)).2,
      fun _ _ => rfl, fun _ _ _ => rfl, Mem.Agree.refl _ _, rfl, rfl, rfl, rfl, rfl⟩
  | o :: os, init, s, hwf, hl, hi => by
    obtain ⟨w1, w2, w3, w4⟩ := FProg.wf_cons hwf
    apply WP.seq
    refine WP.mono (op_ok offN offMp base K N o s hl w2 w3 (fun i hi' => (hi i (w1 i hi')).2)) ?_
    intro q1 h1
    have hi1 : ∀ i ∈ o.dst :: init, i < K ∧ slotVal base q1 i < N := by
      intro i hmem
      rcases List.mem_cons.mp hmem with e | e
      · subst e; exact ⟨w2, h1.red⟩
      · obtain ⟨a, b⟩ := hi i e
        refine ⟨a, ?_⟩
        by_cases hd : i = o.dst
        · subst hd; exact h1.red
        · rw [h1.others i a hd]; exact b
    refine WP.mono (prog_ok offN offMp base K N os (o.dst :: init) q1 w4 h1.layout hi1) ?_
    intro q h
    have hv1 : ∀ i < K, decode N (slotVal base q1 i) =
        o.run (fun i => decode N (slotVal base s i)) i := by
      intro i hi'
      by_cases hd : i = o.dst
      · subst hd; exact h1.val
      · rw [h1.others i hi' hd]
        cases o <;> simp only [FOp.run, FOp.dst] at hd ⊢ <;> rw [Function.update_of_ne hd]
    have hs1 : slotAddr base q1 0 = slotAddr base s 0 := by unfold slotAddr; rw [h1.r14]
    refine ⟨h.layout, fun i hmem => ?_, fun i hi' => ?_, fun i hi' hnot => ?_, ?_,
      h.r13.trans h1.r13, h.r14.trans h1.r14, h.rd.trans h1.rd, h.wr.trans h1.wr, h.labels.trans h1.labels⟩
    · apply h.red
      simp only [FProg.writes, List.mem_append, List.mem_cons] at hmem ⊢
      tauto
    · rw [h.vals i hi']
      simp only [FProg.run]
      exact FProg.run_congr K os _ w4 _ _ hv1 i hi'
    · simp only [FProg.writes, List.mem_cons, not_or] at hnot
      rw [h.others i hi' hnot.2, h1.others i hi' hnot.1]
    · have := h.agree
      rw [h1.r14] at this
      exact (agree_slot_area base K s hl.hoffs o.dst w2 h1.agree).trans this

end CC.Limb
