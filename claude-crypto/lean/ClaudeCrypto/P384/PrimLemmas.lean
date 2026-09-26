import ClaudeCrypto.P384.Frame

/-!
# Proof support for the primitives of `P384/Prims.lean`

* `St`: the invariant of a loop that stores the six limbs of a frame slot one
  by one (`copySlot`, `copyConst`, `zeroSlot`, `loadBE`), and `st_iter`,
  `st_done`;
* byte-order lemmas for `loadBE`;
* a generic borrow-chain lemma for `ltConst`.
-/

namespace CC.P384

open CC.Limb CC.Spec.P384

theorem nSlots_eq : nSlots = 37 := rfl
theorem frameSize_eq : frameSize = 1784 := rfl
theorem cntOff_eq : cntOff = 1776 := rfl

theorem slotOff_eq (i : Nat) : slotOff i = 48 * i := by simp [slotOff, FOp.off]

theorem slotAddr_eq (s : State) (i : Nat) : slotAddr 0 s i = s.r 14 + BitVec.ofNat 64 (slotOff i) := rfl

/-- Reading outside the changed region `⟨b, L⟩` (trivial if `L = 0`). -/
theorem agree_readW {m m' : Mem} {b : Addr} {L : Nat} (h : Mem.Agree m m' ⟨b, L⟩) (A : Addr)
    (hs : 0 < L → Mem.Sep b L A 8) : m'.readW A 64 = m.readW A 64 := by
  rcases Nat.eq_zero_or_pos L with h0 | h0
  · subst h0
    unfold Mem.readW; congr 1
    apply Mem.read_congr; intro i _
    exact h _ (by unfold Region.Contains; simp)
  · exact h.readW A 64 (hs h0)

/-- The separation of a prefix of slot `d` and a limb at offset `y` of the frame. -/
theorem sep_frame (b : Addr) (x L y : Nat) (h : x + L ≤ y ∨ y + 8 ≤ x) (hx : x + L < 2 ^ 64)
    (hy : y + 8 < 2 ^ 64) : 0 < L → Mem.Sep (b + BitVec.ofNat 64 x) L (b + BitVec.ofNat 64 y) 8 :=
  fun hL => sep_offsets b x y L 8 h hx hy hL (by decide)

/-! ## Storing the limbs of a slot -/

/-- After storing limbs `0..j` of slot `d` (values `vals`), using register 9. -/
structure St (s0 : State) (d : Nat) (vals : Nat → BitVec 64) (j : Nat) (s : State) : Prop where
  regs : ∀ v, v ≠ 9 → s.r v = s0.r v
  r9 : s.r 9 = if j = 0 then s0.r 9 else vals (j - 1)
  cf : s.cf = s0.cf
  sub : s.sub = s0.sub
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  labels : s.labels = s0.labels
  agree : Mem.Agree s0.mem s.mem ⟨slotAddr 0 s0 d, 8 * j⟩
  lim : ∀ k < j, mlimb s.mem (slotAddr 0 s0 d) k = (vals k).toNat

theorem St.init (s0 : State) (d : Nat) (vals : Nat → BitVec 64) : St s0 d vals 0 s0 :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun a _ => rfl, fun k hk => absurd hk (by omega)⟩

theorem St.r14 {s0 s : State} {d : Nat} {vals : Nat → BitVec 64} {j : Nat} (h : St s0 d vals j s) :
    s.r 14 = s0.r 14 := h.regs 14 (by decide)

/-- Loading a word of memory outside the prefix of slot `d` written so far. -/
theorem St.readW {s0 s : State} {d : Nat} {vals : Nat → BitVec 64} {j : Nat} (h : St s0 d vals j s) (A : Addr)
    (hs : 0 < 8 * j → Mem.Sep (slotAddr 0 s0 d) (8 * j) A 8) : s.mem.readW A 64 = s0.mem.readW A 64 :=
  agree_readW h.agree A hs

theorem exec1_some {i : Instr} {s s' : State} (h : isa.exec i s = some s') :
    ∃ tr, execBlock isa [i] s = some (s', tr) := by
  refine ⟨(addrs i s).map Leak.addr, ?_⟩
  have h' : exec i s = some s' := h
  simp [execBlock, isa, h']

def stBody (pre : Nat → List Instr) (d : Nat) (k : Nat) : List Instr := pre k ++ [.st 14 (slotOff d + 8 * k) 9]

theorem st_step (s0 : State) (h : Inv s0) (d : Nat) (hd : d < nSlots) (pre : Nat → List Instr)
    (vals : Nat → BitVec 64)
    (hpre : ∀ k < 6, ∀ s, St s0 d vals k s → ∃ tr, execBlock isa (pre k) s = some (s.set 9 (vals k), tr))
    (k : Nat) (hk : k < 6) (s : State) (hs : St s0 d vals k s) :
    ∃ q, execBlock isa (stBody pre d k) s = some q ∧ St s0 d vals (k + 1) q.1 := by
  obtain ⟨tr, htr⟩ := hpre k hk s hs
  have hA : s.r 14 + BitVec.ofNat 64 (slotOff d + 8 * k) = slotAddr 0 s0 d + BitVec.ofNat 64 (8 * k) := by
    rw [hs.r14, slotAddr_eq, addr_add_ofNat']
  have hp : InRegions s.wr (s.r 14 + BitVec.ofNat 64 (slotOff d + 8 * k)) 8 := by
    rw [hs.wr, hs.r14]; exact slot_in s0 h d hd k hk
  set v := vals k
  have hp' : InRegions (s.set 9 v).wr ((s.set 9 v).r 14 + BitVec.ofNat 64 (slotOff d + 8 * k)) 8 := by
    simpa [Limb.State.set, Function.update_of_ne (show (14 : Var) ≠ 9 by decide)] using hp
  obtain ⟨tr', hq⟩ : ∃ tr', execBlock isa (stBody pre d k) s =
      some ({ s.set 9 v with mem := s.mem.writeW (slotAddr 0 s0 d + BitVec.ofNat 64 (8 * k)) v }, tr') := by
    rw [stBody, execBlock_append, htr, Option.bind_some]
    simp only [execBlock, isa, Limb.exec, Limb.State.store, hp', ite_true, Option.map_some]
    simp only [Limb.State.set, Function.update_of_ne (show (14 : Var) ≠ 9 by decide), Function.update_self, hA]
    exact ⟨_, rfl⟩
  refine ⟨_, hq, ?_⟩
  refine ⟨fun v' hv => ?_, ?_, hs.cf, hs.sub, hs.rd, hs.wr, hs.labels, ?_, fun j hj => ?_⟩
  · simp only [Limb.State.set, Function.update_of_ne hv]; exact hs.regs v' hv
  · simp [Limb.State.set, v]
  · refine (hs.agree.widen (by omega)).writeW _ _ ?_
    exact Region.contains_offset _ _ _ _ (by omega) (by omega)
  · unfold mlimb
    simp only
    rcases Nat.lt_or_ge j k with hj' | hj'
    · rw [Mem.readW_writeW_sep _ _ _ _ _ (sep_offsets _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
        (by omega))]
      exact hs.lim j hj'
    · have : j = k := by omega
      subst this
      rw [Mem.readW_writeW_same_64]

theorem st_iter (s0 : State) (h : Inv s0) (d : Nat) (hd : d < nSlots) (pre : Nat → List Instr)
    (vals : Nat → BitVec 64)
    (hpre : ∀ k < 6, ∀ s, St s0 d vals k s → ∃ tr, execBlock isa (pre k) s = some (s.set 9 (vals k), tr)) :
    ∃ q, execBlock isa ((List.range 6).flatMap (stBody pre d)) s0 = some q ∧ St s0 d vals 6 q.1 := by
  have := WP.block_iter (M := isa) (stBody pre d) (St s0 d vals) 0 6
    (fun i hi s hs => by
      obtain ⟨q, hq, hq'⟩ := st_step s0 h d hd pre vals hpre (0 + i) (by omega) s hs
      exact WP.block_intro q hq hq') s0 (St.init s0 d vals)
  obtain ⟨t, s', he, hs'⟩ := this
  cases he with
  | block he =>
    refine ⟨(s', t), ?_, hs'⟩
    rw [← he, List.flatMap_def]
    simp

/-- Changing only slot `d` (and registers other than 13, 14). -/
theorem eff_of_slot_agree {s0 q : State} (d : Nat) (hd : d < nSlots) (h13 : q.r 13 = s0.r 13)
    (h14 : q.r 14 = s0.r 14) (hrd : q.rd = s0.rd) (hwr : q.wr = s0.wr) (hl : q.labels = s0.labels)
    (hag : Mem.Agree s0.mem q.mem ⟨slotAddr 0 s0 d, 48⟩) : Eff [d] s0 q := by
  have harea := agree_slot_area 0 nSlots s0 (by decide) d hd hag
  refine ⟨frm_of_agree h13 h14 hrd hwr hl harea, fun i hi hne => ?_, cnt_of_agree h14 harea⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hne
  unfold sv slotVal mval
  rw [show slotAddr 0 q i = slotAddr 0 s0 i by rw [slotAddr, slotAddr, h14]]
  apply lsum_congr; intro k hk
  unfold mlimb
  rw [hag.readW _ _ (slot_sep 0 nSlots s0 (by decide) i d hi hd hne k hk)]

theorem st_done (s0 : State) (d : Nat) (hd : d < nSlots) (vals : Nat → BitVec 64) (q : State)
    (hq : St s0 d vals 6 q) :
    Eff [d] s0 q ∧ sv q d = lsum (fun k => (vals k).toNat) 6 ∧ (∀ v, v ≠ 9 → q.r v = s0.r v) ∧
      q.cf = s0.cf ∧ q.sub = s0.sub := by
  have h14 := hq.r14
  refine ⟨eff_of_slot_agree d hd (hq.regs 13 (by decide)) h14 hq.rd hq.wr hq.labels hq.agree, ?_, hq.regs,
    hq.cf, hq.sub⟩
  unfold sv slotVal mval
  rw [show slotAddr 0 q d = slotAddr 0 s0 d by rw [slotAddr, slotAddr, h14]]
  exact lsum_congr _ _ _ hq.lim

/-! ## Byte order -/

/-- The `len` bytes at `a`. -/
def inBytes (m : Mem) (a : Addr) (len : Nat) : List (BitVec 8) :=
  (List.range len).map fun j => m (a + BitVec.ofNat 64 j)

theorem length_inBytes (m : Mem) (a : Addr) (len : Nat) : (inBytes m a len).length = len := by
  simp [inBytes]

theorem inBytes_add (m : Mem) (a : Addr) (p q : Nat) :
    inBytes m a (p + q) = inBytes m a p ++ inBytes m (a + BitVec.ofNat 64 p) q := by
  unfold inBytes
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left; intro j _
  simp only [Function.comp, addr_add_ofNat']

theorem foldl_bytes (ys : List (BitVec 8)) (acc : Nat) :
    ys.foldl (fun acc x => 256 * acc + x.toNat) acc =
      acc * 256 ^ ys.length + ys.foldl (fun acc x => 256 * acc + x.toNat) 0 := by
  induction ys generalizing acc with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (256 * 0 + y.toNat)]
    ring

theorem bytesToNat_append (xs ys : List (BitVec 8)) :
    bytesToNat (xs ++ ys) = bytesToNat xs * 256 ^ ys.length + bytesToNat ys := by
  unfold bytesToNat
  rw [List.foldl_append, foldl_bytes]

theorem toNat_append' {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-- Byte `i` of a little-endian load. -/
theorem readW_byte (m : Mem) (a : Addr) (i : Nat) (hi : i < 8) :
    (m.readW a 64).extractLsb' (8 * i) 8 = m (a + BitVec.ofNat 64 i) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [Mem.readW, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_setWidth,
    Mem.getLsbD_read]
  have e1 : (8 * i + j) / 8 = i := by omega
  have e2 : (8 * i + j) % 8 = j := by omega
  simp [e1, e2, show 8 * i + j < 64 by omega]

/-- `ldbe` reads a big-endian word. -/
theorem bswap64_readW (m : Mem) (a : Addr) : (bswap64 (m.readW a 64)).toNat = bytesToNat (inBytes m a 8) := by
  have b0 := readW_byte m a 0 (by decide); have b1 := readW_byte m a 1 (by decide)
  have b2 := readW_byte m a 2 (by decide); have b3 := readW_byte m a 3 (by decide)
  have b4 := readW_byte m a 4 (by decide); have b5 := readW_byte m a 5 (by decide)
  have b6 := readW_byte m a 6 (by decide); have b7 := readW_byte m a 7 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at b0 b1 b2 b3 b4 b5 b6 b7
  simp only [bswap64, toNat_append', b0, b1, b2, b3, b4, b5, b6, b7]
  simp only [bytesToNat, inBytes, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, List.foldl_cons, List.foldl_nil]
  ring

set_option exponentiation.threshold 400 in
/-- Six big-endian words, most significant first, as little-endian limbs. -/
theorem bytesToNat_48 (m : Mem) (a : Addr) :
    bytesToNat (inBytes m a 48) =
      lsum (fun k => bytesToNat (inBytes m (a + BitVec.ofNat 64 (40 - 8 * k)) 8)) 6 := by
  rw [show (48 : Nat) = 8 + (8 + (8 + (8 + (8 + 8)))) from rfl]
  simp only [inBytes_add, addr_add_ofNat', bytesToNat_append, List.length_append, length_inBytes]
  simp only [lsum, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, zero_add]
  have e : a + 0#64 = a := by simp
  simp only [e, Nat.reducePow]
  ring

/-! ## Iterating blocks -/

theorem exec_iter (f : Nat → List Instr) (I : Nat → State → Prop) (a n : Nat)
    (hstep : ∀ i < n, ∀ s, I (a + i) s → ∃ q, execBlock isa (f (a + i)) s = some q ∧ I (a + i + 1) q.1)
    (s : State) (hs : I a s) :
    ∃ q, execBlock isa ((List.range n).map (fun i => f (a + i))).flatten s = some q ∧ I (a + n) q.1 := by
  obtain ⟨t, s', he, hs'⟩ := WP.block_iter (M := isa) f I a n (fun i hi s hs => by
    obtain ⟨q, hq, hq'⟩ := hstep i hi s hs
    exact WP.block_intro q hq hq') s hs
  cases he with
  | block he => exact ⟨(s', t), he, hs'⟩

/-! ## Borrow chains -/

/-- The borrow of a multi-limb comparison, one limb at a time. -/
theorem lt_limb (LA LC W x y : Nat) (hA : LA < W) (hC : LC < W) :
    (LA + x * W < LC + y * W) ↔ (x < y + (if LA < LC then 1 else 0)) := by
  have key : ∀ u v, u ≤ v → u * W ≤ v * W := fun u v h => Nat.mul_le_mul_right W h
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have h1 := key (x + 1) y hxy
    rw [Nat.add_mul, Nat.one_mul] at h1
    generalize x * W = P at *; generalize y * W = Q at *
    split_ifs <;> omega
  · generalize x * W = P
    split_ifs <;> omega
  · have h1 := key (y + 1) x hxy
    rw [Nat.add_mul, Nat.one_mul] at h1
    generalize x * W = P at *; generalize y * W = Q at *
    split_ifs <;> omega

theorem borrowOut_lsum (A C : Nat → Nat) (j : Nat) (hA : ∀ k, A k < 2 ^ 64) (hC : ∀ k, C k < 2 ^ 64)
    (x y : BitVec 64) (hx : x.toNat = A j) (hy : y.toNat = C j) :
    borrowOut x y (decide (lsum A j < lsum C j)) = decide (lsum A (j + 1) < lsum C (j + 1)) := by
  have hLA := lsum_lt A j (fun k _ => hA k)
  have hLC := lsum_lt C j (fun k _ => hC k)
  rw [lsum_succ, lsum_succ, Nat.mul_comm (A j), Nat.mul_comm (C j), Nat.add_comm (lsum A j),
    Nat.add_comm (lsum C j)]
  rw [Nat.add_comm (_ * _) (lsum A j), Nat.add_comm (_ * _) (lsum C j), Nat.mul_comm, Nat.mul_comm (2 ^ _)]
  unfold borrowOut
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff, lt_limb _ _ _ _ _ hLA hLC, hx, hy]
  by_cases h : lsum A j < lsum C j <;> simp [h]

theorem exec_append {l₁ l₂ : List Instr} {s : State} {q₁ q₂ : State × List Leak}
    (h₁ : execBlock isa l₁ s = some q₁) (h₂ : execBlock isa l₂ q₁.1 = some q₂) :
    execBlock isa (l₁ ++ l₂) s = some (q₂.1, q₁.2 ++ q₂.2) := by
  rw [execBlock_append, h₁]; simp [h₂]

/-! ## Comparison with a constant -/

def cmpA (s0 : State) (a : Nat) (k : Nat) : Nat := mlimb s0.mem (slotAddr 0 s0 a) k
def cmpC (s0 : State) (c : Nat) (k : Nat) : Nat := mlimb s0.mem (s0.r 13 + BitVec.ofNat 64 c) k

structure LtInv (s0 : State) (a c : Nat) (j : Nat) (s : State) : Prop where
  regs : ∀ v, v ≠ 8 → v ≠ 9 → s.r v = s0.r v
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  labels : s.labels = s0.labels
  cf : s.cf = some (decide (lsum (cmpA s0 a) j < lsum (cmpC s0 c) j))
  sub : s.sub = true

def ltBody (a c j : Nat) : List Instr := [.ld 9 14 (slotOff a + 8 * j), .ld 8 13 (c + 8 * j), .sbb 9 8]

theorem mlimb_lt (m : Mem) (a : Addr) (k : Nat) : mlimb m a k < 2 ^ 64 := by
  unfold mlimb; exact BitVec.isLt _

/-- Limb `j` of the comparison (`sbb`, or `sub` for the first limb). -/
theorem lt_step (s0 : State) (h : Inv s0) (a c : Nat) (ha : a < nSlots) (hc : c + 48 ≤ constSize) (j : Nat)
    (hj : j < 6) (s : State) (first : Bool) (hfirst : first = true → j = 0)
    (hcf : first = false → s.cf = some (decide (lsum (cmpA s0 a) j < lsum (cmpC s0 c) j)) ∧ s.sub = true)
    (hr : ∀ v, v ≠ 8 → v ≠ 9 → s.r v = s0.r v) (hm : s.mem = s0.mem) (hrd : s.rd = s0.rd) (hwr : s.wr = s0.wr)
    (hl : s.labels = s0.labels) :
    ∃ q, execBlock isa [.ld 9 14 (slotOff a + 8 * j), .ld 8 13 (c + 8 * j), if first then .sub 9 8 else .sbb 9 8] s
      = some q ∧ LtInv s0 a c (j + 1) q.1 := by
  have r13 : s.r 13 = s0.r 13 := hr 13 (by decide) (by decide)
  have r14 : s.r 14 = s0.r 14 := hr 14 (by decide) (by decide)
  have p1 : InRegions (s.rd ++ s.wr) (s.r 14 + BitVec.ofNat 64 (slotOff a + 8 * j)) 8 := by
    rw [hrd, hwr, r14]; exact (inRegions_append _ _ _ _).mpr (Or.inr (slot_in s0 h a ha j hj))
  have p2 : InRegions (s.rd ++ s.wr) (s.r 13 + BitVec.ofNat 64 (c + 8 * j)) 8 := by
    rw [hrd, hwr, r13]; exact const_in s0 h _ (by omega)
  have eA : (s.mem.readW (s.r 14 + BitVec.ofNat 64 (slotOff a + 8 * j)) 64).toNat = cmpA s0 a j := by
    rw [hm, r14, cmpA, mlimb, slotAddr_eq, addr_add_ofNat']
  have eC : (s.mem.readW (s.r 13 + BitVec.ofNat 64 (c + 8 * j)) 64).toNat = cmpC s0 c j := by
    rw [hm, r13, cmpC, mlimb, addr_add_ofNat']
  have hb := borrowOut_lsum (cmpA s0 a) (cmpC s0 c) j (fun k => mlimb_lt _ _ _) (fun k => mlimb_lt _ _ _) _ _ eA eC
  have fin : ∀ q : State, (∀ v, v ≠ 8 → v ≠ 9 → q.r v = s.r v) →
      q.mem = s.mem → q.rd = s.rd → q.wr = s.wr → q.labels = s.labels → q.sub = true →
      q.cf = some (decide (lsum (cmpA s0 a) (j + 1) < lsum (cmpC s0 c) (j + 1))) → LtInv s0 a c (j + 1) q :=
    fun q e1 e2 e3 e4 e5 e6 e7 => ⟨fun v h8 h9 => by rw [e1 v h8 h9]; exact hr v h8 h9,
      e2.trans hm, e3.trans hrd, e4.trans hwr, e5.trans hl, e7, e6⟩
  cases first
  · obtain ⟨hc1, hs1⟩ := hcf rfl
    simp only [Bool.false_eq_true, ite_false]
    limb_sym [p1, p2, hc1, hs1]
    refine ⟨_, rfl, fin _ ?_ rfl rfl rfl rfl rfl ?_⟩
    · intro v h8 h9; simp [Function.update_of_ne h8, Function.update_of_ne h9]
    · rw [← hb]
  · have hj0 := hfirst rfl; subst hj0
    simp only [ite_true]
    limb_sym [p1, p2]
    refine ⟨_, rfl, fin _ ?_ rfl rfl rfl rfl rfl ?_⟩
    · intro v h8 h9; simp [Function.update_of_ne h8, Function.update_of_ne h9]
    · rw [← hb]; simp [lsum]

/-! ## Shifting a slot left by one bit -/

theorem agree_down {m m' : Mem} {b : Addr} {x L x' L' : Nat} (h : Mem.Agree m m' ⟨b + BitVec.ofNat 64 x, L⟩)
    (hx : x' ≤ x) (hL : x + L ≤ x' + L') (hb : x' + L' < 2 ^ 64) :
    Mem.Agree m m' ⟨b + BitVec.ofNat 64 x', L'⟩ := by
  intro a ha
  apply h a
  intro hc
  apply ha
  unfold Region.Contains at *
  simp only at *
  have e : a - (b + BitVec.ofNat 64 x') = (a - (b + BitVec.ofNat 64 x)) + BitVec.ofNat 64 (x - x') := by
    rw [show a - (b + BitVec.ofNat 64 x) + BitVec.ofNat 64 (x - x') =
      a - (b + (BitVec.ofNat 64 x - BitVec.ofNat 64 (x - x'))) by abel]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := (a - (b + BitVec.ofNat 64 x)).isLt
  rw [Nat.mod_eq_of_lt (a := x - x') (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

def tbA (s0 : State) (a k : Nat) : BitVec 64 := s0.mem.readW (slotAddr 0 s0 a + BitVec.ofNat 64 (8 * k)) 64

def tbN (s0 : State) (a k : Nat) : BitVec 64 :=
  if k = 0 then tbA s0 a 0 <<< 1 else (tbA s0 a k <<< 1) ||| (tbA s0 a (k - 1) >>> 63)

/-- After shifting limbs `[6 - j, 6)`. -/
structure TB (s0 : State) (a : Nat) (d : Var) (j : Nat) (s : State) : Prop where
  regs : ∀ v, v ≠ d → v ≠ 7 → v ≠ 8 → s.r v = s0.r v
  rdv : s.r d = tbA s0 a 5 >>> 63
  cf : s.cf = none
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  labels : s.labels = s0.labels
  agree : Mem.Agree s0.mem s.mem ⟨slotAddr 0 s0 a + BitVec.ofNat 64 (48 - 8 * j), 8 * j⟩
  lim : ∀ k < 6, 6 - j ≤ k → mlimb s.mem (slotAddr 0 s0 a) k = (tbN s0 a k).toNat

theorem TB.read {s0 s : State} {a : Nat} {d : Var} {j : Nat} (h : TB s0 a d j s) (hd14 : d ≠ 14) (i : Nat)
    (hi : i + j < 6) (ha : a < nSlots) :
    s.mem.readW (s.r 14 + BitVec.ofNat 64 (slotOff a + 8 * i)) 64 = tbA s0 a i := by
  rw [h.regs 14 (Ne.symm hd14) (by decide) (by decide), ← addr_add_ofNat', ← slotAddr_eq, tbA]
  refine agree_readW h.agree _ (fun _ => ?_)
  rw [slotAddr_eq, addr_add_ofNat', addr_add_ofNat', slotOff_eq]
  exact sep_offsets _ _ _ _ _ (by omega) (by have := nSlots_eq; omega) (by have := nSlots_eq; omega)
    (by omega) (by decide)

theorem shl1_toNat (x : BitVec 64) : (x <<< 1).toNat = 2 * (x.toNat % 2 ^ 63) := by
  have := x.isLt
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, pow_one]
  omega

theorem shr63_toNat (x : BitVec 64) : (x >>> 63).toNat = x.toNat / 2 ^ 63 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem shl_or_shr_toNat (x y : BitVec 64) :
    ((x <<< 1) ||| (y >>> 63)).toNat = 2 * (x.toNat % 2 ^ 63) + y.toNat / 2 ^ 63 := by
  have hand : (x <<< 1) &&& (y >>> 63) = 0 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    by_cases h0 : i = 0
    · subst h0; simp
    · have : y.getLsbD (63 + i) = false := BitVec.getLsbD_of_ge y _ (by omega)
      simp [this]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand, BitVec.toNat_add, shl1_toNat, shr63_toNat]
  have := x.isLt; have := y.isLt
  apply Nat.mod_eq_of_lt
  have : y.toNat / 2 ^ 63 < 2 := by omega
  omega

theorem tbN_toNat (s0 : State) (a k : Nat) :
    (tbN s0 a k).toNat = 2 * ((tbA s0 a k).toNat % 2 ^ 63) +
      (if k = 0 then 0 else (tbA s0 a (k - 1)).toNat / 2 ^ 63) := by
  unfold tbN
  split_ifs with h
  · subst h; rw [shl1_toNat]; rfl
  · rw [shl_or_shr_toNat]

set_option exponentiation.threshold 400 in
theorem topBit_math (A : Nat → Nat) (hA : ∀ k, A k < 2 ^ 64) :
    lsum (fun k => 2 * (A k % 2 ^ 63) + (if k = 0 then 0 else A (k - 1) / 2 ^ 63)) 6 = 2 * lsum A 6 % 2 ^ 384 ∧
      lsum A 6 / 2 ^ 383 = A 5 / 2 ^ 63 := by
  have h0 := hA 0; have h1 := hA 1; have h2 := hA 2; have h3 := hA 3; have h4 := hA 4; have h5 := hA 5
  simp only [lsum, Nat.reduceMul, Nat.reducePow, Nat.zero_add, Nat.mul_one, ite_true, Nat.add_zero,
    ite_false, Nat.succ_ne_zero, Nat.add_one_sub_one, Nat.reduceSub, OfNat.ofNat_ne_zero]
  omega

def tbGroup (a k : Nat) : List Instr :=
  [.ld 7 14 (slotOff a + 8 * k), .shl 7 1, .ld 8 14 (slotOff a + 8 * (k - 1)), .shr 8 63, .or 7 8,
   .st 14 (slotOff a + 8 * k) 7]

theorem tb_step (s0 : State) (h : Inv s0) (a : Nat) (ha : a < nSlots) (d : Var) (hd7 : d ≠ 7) (hd8 : d ≠ 8)
    (hd14 : d ≠ 14) (j : Nat) (hj : j < 5) (s : State) (hs : TB s0 a d j s) :
    ∃ q, execBlock isa (tbGroup a (5 - j)) s = some q ∧ TB s0 a d (j + 1) q.1 := by
  have r14 : s.r 14 = s0.r 14 := hs.regs 14 (Ne.symm hd14) (by decide) (by decide)
  have e1 := hs.read hd14 (5 - j) (by omega) ha
  have e2 := hs.read hd14 (5 - j - 1) (by omega) ha
  have p1 : InRegions (s.rd ++ s.wr) (s.r 14 + BitVec.ofNat 64 (slotOff a + 8 * (5 - j))) 8 := by
    rw [hs.rd, hs.wr, r14]; exact (inRegions_append _ _ _ _).mpr (Or.inr (slot_in s0 h a ha _ (by omega)))
  have p2 : InRegions (s.rd ++ s.wr) (s.r 14 + BitVec.ofNat 64 (slotOff a + 8 * (5 - j - 1))) 8 := by
    rw [hs.rd, hs.wr, r14]; exact (inRegions_append _ _ _ _).mpr (Or.inr (slot_in s0 h a ha _ (by omega)))
  have p3 : InRegions s.wr (s.r 14 + BitVec.ofNat 64 (slotOff a + 8 * (5 - j))) 8 := by
    rw [hs.wr, r14]; exact slot_in s0 h a ha _ (by omega)
  have hA : s.r 14 + BitVec.ofNat 64 (slotOff a + 8 * (5 - j)) =
      slotAddr 0 s0 a + BitVec.ofNat 64 (48 - 8 * (j + 1)) := by
    rw [r14, slotAddr_eq, addr_add_ofNat']; congr 2; omega
  simp only [tbGroup]
  limb_sym [p1, p2, p3, e1, e2]
  refine ⟨_, rfl, ⟨fun v h1 h2 h3 => ?_, ?_, rfl, hs.rd, hs.wr, hs.labels, ?_, fun k hk hk' => ?_⟩⟩
  · simp only [Function.update_of_ne h2, Function.update_of_ne h3]; exact hs.regs v h1 h2 h3
  · simp only [Function.update_of_ne hd7, Function.update_of_ne hd8]; exact hs.rdv
  · rw [hA]
    refine (agree_down hs.agree (by omega) (by omega) (by rw [slotOff_eq] at *; omega)).writeW _ _ ?_
    exact (region_contains_self _ _ _).mpr (by omega)
  · unfold mlimb
    rw [hA]
    rcases Nat.lt_or_ge k (5 - j) with hk1 | hk1
    · omega
    rcases Nat.lt_or_ge (5 - j) k with hk2 | hk2
    · rw [Mem.readW_writeW_sep _ _ _ _ _
        (sep_offsets _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega))]
      exact hs.lim k hk (by omega)
    · have hk3 : k = 5 - j := by omega
      subst hk3
      rw [show 8 * (5 - j) = 48 - 8 * (j + 1) by omega, Mem.readW_writeW_same_64]
      simp [tbN, show 5 - j ≠ 0 by omega]

theorem tb_init (s0 : State) (h : Inv s0) (a : Nat) (ha : a < nSlots) (d : Var) (hd14 : d ≠ 14) :
    ∃ q, execBlock isa [.ld d 14 (slotOff a + 40), .shr d 63] s0 = some q ∧ TB s0 a d 0 q.1 := by
  have p1 : InRegions (s0.rd ++ s0.wr) (s0.r 14 + BitVec.ofNat 64 (slotOff a + 40)) 8 :=
    (inRegions_append _ _ _ _).mpr (Or.inr (slot_in s0 h a ha 5 (by decide)))
  have e1 : s0.mem.readW (s0.r 14 + BitVec.ofNat 64 (slotOff a + 40)) 64 = tbA s0 a 5 := by
    rw [tbA, slotAddr_eq, addr_add_ofNat']
  limb_sym [p1, e1, hd14]
  refine ⟨_, rfl, ⟨fun v h1 _ _ => ?_, ?_, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun k hk hk' => by omega⟩⟩
  · simp [Function.update_of_ne h1]
  · simp

theorem tb_last (s0 : State) (h : Inv s0) (a : Nat) (ha : a < nSlots) (d : Var) (hd7 : d ≠ 7) (hd8 : d ≠ 8)
    (hd14 : d ≠ 14) (s : State) (hs : TB s0 a d 5 s) :
    ∃ q, execBlock isa [.ld 7 14 (slotOff a), .shl 7 1, .st 14 (slotOff a) 7] s = some q ∧
      TB s0 a d 6 q.1 := by
  have r14 : s.r 14 = s0.r 14 := hs.regs 14 (Ne.symm hd14) (by decide) (by decide)
  have e1 := hs.read hd14 0 (by omega) ha
  simp only [Nat.mul_zero, Nat.add_zero] at e1
  have p1 : InRegions (s.rd ++ s.wr) (s.r 14 + BitVec.ofNat 64 (slotOff a)) 8 := by
    rw [hs.rd, hs.wr, r14]
    have := slot_in s0 h a ha 0 (by decide); simp only [Nat.mul_zero, Nat.add_zero] at this
    exact (inRegions_append _ _ _ _).mpr (Or.inr this)
  have p3 : InRegions s.wr (s.r 14 + BitVec.ofNat 64 (slotOff a)) 8 := by
    rw [hs.wr, r14]
    have := slot_in s0 h a ha 0 (by decide); simp only [Nat.mul_zero, Nat.add_zero] at this
    exact this
  have hA : s.r 14 + BitVec.ofNat 64 (slotOff a) = slotAddr 0 s0 a + BitVec.ofNat 64 (48 - 8 * 6) := by
    rw [r14, slotAddr_eq]; simp
  limb_sym [p1, p3, e1]
  refine ⟨_, rfl, ⟨fun v h1 h2 h3 => ?_, ?_, rfl, hs.rd, hs.wr, hs.labels, ?_, fun k hk hk' => ?_⟩⟩
  · simp only [Function.update_of_ne h2]; exact hs.regs v h1 h2 h3
  · simp only [Function.update_of_ne hd7]; exact hs.rdv
  · rw [hA]
    refine (agree_down hs.agree (by omega) (by omega) (by rw [slotOff_eq] at *; omega)).writeW _ _ ?_
    exact (region_contains_self _ _ _).mpr (by omega)
  · unfold mlimb
    rw [hA]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      simp [tbN]
    · rw [Mem.readW_writeW_sep _ _ _ _ _
        (sep_offsets _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega))]
      exact hs.lim k hk (by omega)

end CC.P384
