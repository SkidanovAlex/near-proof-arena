import ZkFormal.NearV3.D1.Extract.WalkU.Proof

/-!
# `ZkFormal.NearV3.D1.Extract.WalkU.Proof2` — the `walkU` view: rows, traffic, `walkU_view`

Lane `v3-d1-a7b`.  A copy of D0a's `Extract/WalkProof2.lean` for `walkU`: the stub mode `4`
(`SEDGE`), `UKEYNIB` in place of `KEYNIB`, no `FINAL`.
-/

namespace ZkFormal.NearV3.D1.WalkUProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3 ZkFormal.NearV3.WalkV3
  ZkFormal.NearV3.D1.WalkU

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Row mode as a natural. -/
def modeOf (tr : Trace Fp) (tt q : Nat) : Nat :=
  if tr.cell tt q mS = 1 then 0 else if tr.cell tt q mK = 1 then 1 else if tr.cell tt q mB = 1 then 2
  else if tr.cell tt q mT = 1 then 4 else 3

/-- The symbol slot of the row: the edge's nibble, or, on a stub row, `z` (`zE`). -/
def zAt (tr : Trace Fp) (tt q : Nat) : Nat :=
  if tr.cell tt q mT = 1 then (if tr.cell tt q mW = 1 then SYM_WILD else (tr.cell tt q sym).toNat)
  else (tr.cell tt q nib).toNat

def edgeAt (tr : Trace Fp) (tt q : Nat) : Msg :=
  [(tr.cell tt q nN).toNat, (tr.cell tt q nI).toNat, zAt tr tt q, (tr.cell tt q nN2).toNat,
    (tr.cell tt q nI2).toNat, (tr.cell tt q ek).toNat]

def bmAt (tr : Trace Fp) (tt q : Nat) : Nat := bitsVal (fun b => cv tr tt q (bmb b)) 0 16

def stepAt (tr : Trace Fp) (tt q : Nat) : WStep3 :=
  ⟨modeOf tr tt q, (tr.cell tt q sym).toNat, edgeAt tr tt q, (tr.cell tt q u).toNat, bmAt tr tt q,
    (tr.cell tt q hv).toNat, (tr.cell tt q ub).toNat⟩

def walkOfSeg (tr : Trace Fp) (tt : Nat) (p : Nat × Nat) : WalkR :=
  ⟨(tr.cell tt p.1 w).toNat, (tr.cell tt p.1 tau).toNat, (List.range p.2).map fun j => stepAt tr tt (p.1 + j)⟩

/-- One-hot modes on an active row. -/
theorem modes_cases (hL : TableLocal WalkU.table tr tt pub) {q : Nat} (hq : q < tr.height tt)
    (ha : tr.cell tt q act = 1) :
    (tr.cell tt q mS = 1 ∧ tr.cell tt q mK = 0 ∧ tr.cell tt q mB = 0 ∧ tr.cell tt q mD = 0 ∧ tr.cell tt q mT = 0) ∨
    (tr.cell tt q mS = 0 ∧ tr.cell tt q mK = 1 ∧ tr.cell tt q mB = 0 ∧ tr.cell tt q mD = 0 ∧ tr.cell tt q mT = 0) ∨
    (tr.cell tt q mS = 0 ∧ tr.cell tt q mK = 0 ∧ tr.cell tt q mB = 1 ∧ tr.cell tt q mD = 0 ∧ tr.cell tt q mT = 0) ∨
    (tr.cell tt q mS = 0 ∧ tr.cell tt q mK = 0 ∧ tr.cell tt q mB = 0 ∧ tr.cell tt q mD = 1 ∧ tr.cell tt q mT = 0) ∨
    (tr.cell tt q mS = 0 ∧ tr.cell tt q mK = 0 ∧ tr.cell tt q mB = 0 ∧ tr.cell tt q mD = 0 ∧ tr.cell tt q mT = 1) := by
  have hm := (rowFacts hL hq).2.1
  rw [ha] at hm
  rcases isBool hL hq bc_mS with h1 | h1 <;> rcases isBool hL hq bc_mK with h2 | h2 <;>
    rcases isBool hL hq bc_mB with h3 | h3 <;> rcases isBool hL hq bc_mD with h4 | h4 <;>
    rcases isBool hL hq bc_mT with h5 | h5 <;>
    rw [h1, h2, h3, h4, h5] at hm <;> first | (exfalso; revert hm; decide) | simp [h1, h2, h3, h4, h5]

theorem modeOf_le (q : Nat) : modeOf tr tt q ≤ 4 := by
  unfold modeOf
  by_cases h1 : tr.cell tt q mS = 1
  · simp [h1]
  · by_cases h2 : tr.cell tt q mK = 1
    · simp [h1, h2]
    · by_cases h3 : tr.cell tt q mB = 1
      · simp [h1, h2, h3]
      · by_cases h4 : tr.cell tt q mT = 1 <;> simp [h1, h2, h3, h4]

theorem mode0 {q : Nat} (h : modeOf tr tt q = 0) : tr.cell tt q mS = 1 := by
  unfold modeOf at h
  by_cases h1 : tr.cell tt q mS = 1
  · exact h1
  · by_cases h2 : tr.cell tt q mK = 1
    · simp [h1, h2] at h
    · by_cases h3 : tr.cell tt q mB = 1
      · simp [h1, h2, h3] at h
      · by_cases h4 : tr.cell tt q mT = 1 <;> simp [h1, h2, h3, h4] at h

theorem sum_le_len {α : Type} : ∀ (l : List α) (f : α → Nat), (∀ x ∈ l, f x ≤ 1) → (l.map f).sum ≤ l.length
  | [], _, _ => by simp
  | a :: l, f, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h a (by simp); have := sum_le_len l f (fun x hx => h x (by simp [hx])); omega

theorem toNat01 {a : Fp} (h : a = 0 ∨ a = 1) : a.toNat ≤ 1 := by
  rcases h with rfl | rfl <;> decide

theorem toNat_ne {a b : Fp} (h : a ≠ b) : a.toNat ≠ b.toNat := by
  intro e; apply h; rw [← Fp.ofNat_toNat a, ← Fp.ofNat_toNat b, e]

theorem zAt_nib {q : Nat} (h : tr.cell tt q mT = 0) : zAt tr tt q = (tr.cell tt q nib).toNat := by
  simp [zAt, h]

theorem mT0 (hL : TableLocal WalkU.table tr tt pub) {q : Nat} (hq : q < tr.height tt)
    (ha : tr.cell tt q act = 1) (hm : modeOf tr tt q ≠ 4) : tr.cell tt q mT = 0 := by
  rcases modes_cases hL hq ha with h | h | h | h | h
  · exact h.2.2.2.2
  · exact h.2.2.2.2
  · exact h.2.2.2.2
  · exact h.2.2.2.2
  · exfalso; apply hm; simp [modeOf, h]

/-- `StepOkU` of an active row. -/
theorem stepOk (hL : TableLocal WalkU.table tr tt pub) {q : Nat} (hq : q < tr.height tt)
    (ha : tr.cell tt q act = 1) (isL : Bool) (hwe : tr.cell tt q we = if isL then 1 else 0) :
    StepOkU (stepAt tr tt q) isL := by
  obtain ⟨hS, hK, hB, hsum, hidx, hbit⟩ := modeFacts hL hq
  have hrf := rowFacts hL hq
  have t0 : (0 : Fp).toNat = 0 := rfl
  have t1 : (1 : Fp).toNat = 1 := rfl
  refine ⟨?_, by simp [stepAt, edgeAt], fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_,
    fun hl => ?_⟩
  · exact modeOf_le q
  · have hs1 : tr.cell tt q mS = 1 := mode0 hm
    have hT0 := mT0 hL hq ha (by change modeOf tr tt q = 0 at hm; omega)
    obtain ⟨hn, hk0, hk1⟩ := hS hs1
    refine ⟨by simp [stepAt, edgeAt, zAt_nib hT0, hn], fun hl => ?_, fun hl => ?_⟩
    · subst hl; simp at hwe
      have := hk0 hwe
      have : tr.cell tt q ek = 0 ∨ tr.cell tt q ek = 1 := by grind
      rcases this with h | h <;> simp [stepAt, edgeAt, h, t0, t1, EK_DOWN, EK_KEY]
    · subst hl; simp at hwe
      have := hk1 hwe
      simp only [stepAt, edgeAt, List.map_cons, List.map_nil, List.getD_eq_getElem?_getD]
      simp [this, EK_VAL, natCast_eq, Fp.toNat_ofNat, P]
  · have hk1 : tr.cell tt q mK = 1 ∧ tr.cell tt q mS = 0 := by
      change modeOf tr tt q = 1 at hm
      rcases modes_cases hL hq ha with h | h | h | h | h <;> simp [modeOf, h] at hm ⊢ <;> exact h.2.1
    have hT0 := mT0 hL hq ha (by change modeOf tr tt q = 1 at hm; omega)
    obtain ⟨he, hinv⟩ := hK hk1.1
    refine ⟨?_, ?_⟩
    · have : tr.cell tt q ek = (EK_KEY : Nat) ∨ tr.cell tt q ek = (EK_LEND : Nat) := by
        have := he; grind
      rcases this with h | h <;> simp [stepAt, edgeAt, h, EK_KEY, EK_LEND, natCast_eq, Fp.toNat_ofNat, P]
    · have hne : tr.cell tt q nib ≠ tr.cell tt q sym := by
        intro e; rw [e] at hinv; grind
      simpa [stepAt, edgeAt, zAt_nib hT0] using toNat_ne hne
  · have hb1 : tr.cell tt q mB = 1 ∧ tr.cell tt q mS = 0 ∧ tr.cell tt q mK = 0 := by
      change modeOf tr tt q = 2 at hm
      rcases modes_cases hL hq ha with h | h | h | h | h <;> simp [modeOf, h] at hm ⊢ <;> exact ⟨h.2.2.1, h.1, h.2.1⟩
    obtain ⟨hn0, hhv⟩ := hB hb1.1
    have hbits : ∀ b, b < 16 → cv tr tt q (bmb b) ≤ 1 := fun b hb => cv_bool (isBool hL hq (bc_bmb b hb))
    refine ⟨by simp [stepAt, edgeAt, hn0, t0], ?_, toNat01 (isBool hL hq bc_hv), fun hl => ?_, fun hl => ?_⟩
    · simpa [stepAt, bmAt] using bitsVal_lt _ 0 16 (fun b hb => by simpa using hbits b hb)
    · subst hl; simp at hwe; simp [stepAt, hhv hwe, t0]
    · subst hl; simp at hwe
      rw [hb1.1, hwe] at hsum hidx
      have hsel : ∀ j, j < 16 → (c (sel j)).eval tr tt q pub = ((cv tr tt q (sel j) : Nat) : Fp) :=
        fun j _ => by simp [cell_eq_cast]
      rw [selSum, evsum 16 _ _ hsel] at hsum
      have hs1 : ((List.range 16).map fun j => cv tr tt q (sel j)).sum = 1 := by
        have hle : ((List.range 16).map fun j => cv tr tt q (sel j)).sum ≤ 16 := by
          have := sum_le_len (List.range 16) (fun j => cv tr tt q (sel j)) (fun j hj =>
            cv_bool (isBool hL hq (bc_sel j (List.mem_range.1 hj))))
          simpa using this
        apply ofNat_inj (by unfold P; omega) (by unfold P; omega)
        rw [hsum]; grind
      obtain ⟨j0, hj0, hsel0, hsidx, hsbit⟩ := onehot 16 (fun j => cv tr tt q (sel j))
        (fun j hj => cv_bool (isBool hL hq (bc_sel j hj))) hs1
      have hidx' : ∀ j, j < 16 → (smul j (c (sel j))).eval tr tt q pub = ((j * cv tr tt q (sel j) : Nat) : Fp) :=
        fun j _ => by simp [cell_eq_cast, natCast_mul]
      rw [selIdx, evsum 16 _ _ hidx', hsidx] at hidx
      have hsym : tr.cell tt q sym = ((j0 : Nat) : Fp) := by grind
      have hbit' : ∀ j, j < 16 → (Expr.mul (c (sel j)) (c (bmb j))).eval tr tt q pub =
          ((cv tr tt q (sel j) * cv tr tt q (bmb j) : Nat) : Fp) := fun j _ => by simp [cell_eq_cast, natCast_mul]
      rw [selBit, evsum 16 _ _ hbit', hsbit (fun j => cv tr tt q (bmb j))] at hbit
      have hb0 : cv tr tt q (bmb j0) = 0 := by
        have := hbits j0 hj0
        apply ofNat_inj (by unfold P; omega) (by unfold P; omega)
        rw [hbit]; rfl
      have hsymN : (tr.cell tt q sym).toNat = j0 := by
        rw [hsym, toNat_natCast, Nat.mod_eq_of_lt (by unfold P; omega)]
      refine ⟨by simp [stepAt, hsymN, hj0], ?_⟩
      simp only [stepAt, bmAt, hsymN]
      rw [bitsVal_bit _ 16 j0 (fun i hi => hbits i hi) hj0, hb0]
  · have hT1 : tr.cell tt q mT = 1 := by
      change modeOf tr tt q = 4 at hm
      rcases modes_cases hL hq ha with h | h | h | h | h <;> simp [modeOf, h] at hm ⊢ <;> exact h.2.2.2.2
    rcases isBool hL hq bc_mW with hw | hw <;> simp [stepAt, edgeAt, zAt, hT1, hw]
  · subst hl; simp at hwe
    have := (hrf.2.2.2 hwe).2
    simp [stepAt, this, natCast_eq, Fp.toNat_ofNat, SYM_END, P]

/-! ## Row traffic -/

theorem multNat1 (x : Nat) (q : Nat) :
    Interaction.multNat.go tr tt q pub [c x] 0 = if tr.cell tt q x = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_c]
  by_cases h : tr.cell tt q x = 1 <;> simp [h]

theorem multNatSK (q : Nat) :
    Interaction.multNat.go tr tt q pub [.add (c mS) (c mK)] 0 =
      if tr.cell tt q mS + tr.cell tt q mK = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_add, eval_c]
  by_cases h : tr.cell tt q mS + tr.cell tt q mK = 1 <;> simp [h]

def cellsE (tr : Trace Fp) (tt q : Nat) (uu : Fp) : List Fp :=
  [tr.cell tt q nN, tr.cell tt q nI, tr.cell tt q nib, tr.cell tt q nN2, tr.cell tt q nI2, tr.cell tt q ek, uu]

def cellsB (tr : Trace Fp) (tt q : Nat) (pub : List Fp) (uu : Fp) : List Fp :=
  [tr.cell tt q nN, bmE.eval tr tt q pub, tr.cell tt q hv, uu]

def cellsS (tr : Trace Fp) (tt q : Nat) (pub : List Fp) (uu : Fp) : List Fp :=
  [tr.cell tt q nN, tr.cell tt q nI, zE.eval tr tt q pub, uu]

theorem rowT (q : Nat) (b : Nat) (sd : Bool) :
    rowTraffic WalkU.interactions tr tt q pub b sd =
      (if b = B_UKEYNIB ∧ sd = false ∧ tr.cell tt q gK = 1 then
        [[tr.cell tt q w, tr.cell tt q t, tr.cell tt q sym, tr.cell tt q we]] else []) ++
      (if b = B_EDGE ∧ sd = false ∧ tr.cell tt q mS + tr.cell tt q mK = 1 then
        [cellsE tr tt q (tr.cell tt q u)] else []) ++
      (if b = B_EDGE ∧ sd = true ∧ tr.cell tt q mS + tr.cell tt q mK = 1 then
        [cellsE tr tt q (tr.cell tt q u + 1)] else []) ++
      (if b = B_BMAP ∧ sd = false ∧ tr.cell tt q mB = 1 then [cellsB tr tt q pub (tr.cell tt q ub)] else []) ++
      (if b = B_BMAP ∧ sd = true ∧ tr.cell tt q mB = 1 then [cellsB tr tt q pub (tr.cell tt q ub + 1)] else []) ++
      (if b = B_SEDGE ∧ sd = false ∧ tr.cell tt q mT = 1 then [cellsS tr tt q pub (tr.cell tt q u)] else []) ++
      (if b = B_SEDGE ∧ sd = true ∧ tr.cell tt q mT = 1 then [cellsS tr tt q pub (tr.cell tt q u + 1)] else []) := by
  simp only [rowTraffic, WalkU.interactions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Dsl.recv, Dsl.send, Interaction.multNat, multNat1, multNatSK, Interaction.msgVal, WalkV3.edge, WalkV3.bmap,
    WalkU.sedge, List.map_cons, List.map_nil, eval_c, eval_add, eval_k, cellsE, cellsB, cellsS, List.append_assoc]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  refine ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ ?_))))) <;> (split <;> split <;> simp_all [eq_comm]) <;> grind

end ZkFormal.NearV3.D1.WalkUProof

namespace ZkFormal.NearV3.D1.WalkUProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3 ZkFormal.NearV3.WalkV3
  ZkFormal.NearV3.D1.WalkU

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem filter_map_fm {α β : Type} (q : α → Bool) (f : α → β) :
    ∀ l : List α, (l.filter q).map f = l.flatMap fun a => if q a then [f a] else []
  | [] => rfl
  | a :: l => by
    by_cases h : q a = true
    · simp [List.filter_cons, h, filter_map_fm q f l]
    · simp [List.filter_cons, h, filter_map_fm q f l]

theorem sk_iff (hL : TableLocal WalkU.table tr tt pub) {q : Nat} (hq : q < tr.height tt)
    (ha : tr.cell tt q act = 1) :
    (tr.cell tt q mS + tr.cell tt q mK = 1 ↔ modeOf tr tt q ≤ 1) ∧ (tr.cell tt q mB = 1 ↔ modeOf tr tt q = 2) ∧
    (modeOf tr tt q = 0 ↔ tr.cell tt q mS = 1) ∧ (tr.cell tt q mT = 1 ↔ modeOf tr tt q = 4) := by
  rcases modes_cases hL hq ha with h | h | h | h | h <;> simp [modeOf, h] <;> grind

theorem cellsE_eq {q : Nat} (hT : tr.cell tt q mT = 0) (uu : Nat) :
    Msg.toFp ((stepAt tr tt q).edgeMsg uu) = cellsE tr tt q (Fp.ofNat uu) := by
  simp [Msg.toFp, WStep3.edgeMsg, stepAt, edgeAt, zAt_nib hT, cellsE, Fp.ofNat_toNat]

theorem cellsB_eq (hL : TableLocal WalkU.table tr tt pub) {q : Nat} (hq : q < tr.height tt) (uu : Nat) :
    Msg.toFp ((stepAt tr tt q).bmapMsg uu) = cellsB tr tt q pub (Fp.ofNat uu) := by
  have hb : (bmE).eval tr tt q pub = ((bmAt tr tt q : Nat) : Fp) := by
    unfold bmE bmAt
    exact eval_bits tr tt q pub bmb 0 16 (fun b hb => isBool hL hq (by simpa using bc_bmb b (by omega)))
  simp [Msg.toFp, WStep3.bmapMsg, stepAt, edgeAt, cellsB, Fp.ofNat_toNat, hb, natCast_eq]

theorem cellsS_eq (hL : TableLocal WalkU.table tr tt pub) {q : Nat} (hq : q < tr.height tt)
    (hT : tr.cell tt q mT = 1) (uu : Nat) :
    Msg.toFp ((stepAt tr tt q).stubMsg uu) = cellsS tr tt q pub (Fp.ofNat uu) := by
  have hz : Fp.ofNat (zAt tr tt q) = zE.eval tr tt q pub := by
    simp only [zAt, hT, if_true, zE, eval_add, eval_mul, eval_c, eval_sub, eval_k]
    rcases isBool hL hq bc_mW with hw | hw
    · simp [hw, Fp.ofNat_toNat]; grind
    · simp [hw, SYM_WILD, natCast_eq]; grind
  simp [Msg.toFp, WStep3.stubMsg, stepAt, edgeAt, cellsS, Fp.ofNat_toNat, hz]

theorem ite01 (p : Prop) [Decidable p] : (Fp.ofNat (if p then 1 else 0)) = (if p then 1 else 0 : Fp) := by
  split <;> rfl

theorem ofNat_succ (x : Fp) : Fp.ofNat (x.toNat + 1) = x + 1 := by
  rw [← natCast_eq, natCast_add, natCast_eq x.toNat, Fp.ofNat_toNat]; rfl

/-- A segment's rows' traffic on one bus and side, step by step. -/
theorem segStep (hL : TableLocal WalkU.table tr tt pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt ws) (isOne tr tt we) s ℓ)
    (hH : s + ℓ ≤ tr.height tt) (b : Nat) (sd : Bool) (hK : b ≠ B_UKEYNIB) (pm : Nat → Bool)
    (F : WStep3 → Msg)
    (hrow : ∀ j, j < ℓ → rowTraffic WalkU.interactions tr tt (s + j) pub b sd =
      if pm (stepAt tr tt (s + j)).mode then [Msg.toFp (F (stepAt tr tt (s + j)))] else []) :
    (List.range' s ℓ).flatMap (fun q => rowTraffic WalkU.interactions tr tt q pub b sd) =
      ((walkOfSeg tr tt (s, ℓ)).steps.filter (fun st => pm st.mode) |>.map F).map Msg.toFp := by
  rw [filter_map_fm, List.range'_eq_map_range, List.flatMap_map]
  simp only [walkOfSeg, List.flatMap_map, List.map_flatMap]
  apply flatMap_congr'
  intro j hj
  rw [hrow j (List.mem_range.1 hj)]
  split <;> simp

end ZkFormal.NearV3.D1.WalkUProof

namespace ZkFormal.NearV3.D1.WalkUProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3 ZkFormal.NearV3.WalkV3
  ZkFormal.NearV3.D1.WalkU

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem bus_ne : B_UKEYNIB ≠ B_EDGE ∧ B_UKEYNIB ≠ ZkFormal.NearV3.B_BMAP ∧ B_UKEYNIB ≠ B_SEDGE ∧
    B_EDGE ≠ ZkFormal.NearV3.B_BMAP ∧ B_EDGE ≠ B_SEDGE ∧ ZkFormal.NearV3.B_BMAP ≠ B_SEDGE ∧
    B_UKEYNIB ≠ B_KEYNIB := by decide

/-- One row's traffic on `EDGE`, `BMAP`, `SEDGE`. -/
theorem rowMode (hL : TableLocal WalkU.table tr tt pub) {q : Nat} (hq : q < tr.height tt)
    (ha : tr.cell tt q act = 1) (sd : Bool) :
    rowTraffic WalkU.interactions tr tt q pub B_EDGE sd =
      (if (stepAt tr tt q).mode ≤ 1 then
        [Msg.toFp ((stepAt tr tt q).edgeMsg (if sd then (stepAt tr tt q).u + 1 else (stepAt tr tt q).u))]
        else []) ∧
    rowTraffic WalkU.interactions tr tt q pub ZkFormal.NearV3.B_BMAP sd =
      (if (stepAt tr tt q).mode = 2 then
        [Msg.toFp ((stepAt tr tt q).bmapMsg (if sd then (stepAt tr tt q).ub + 1 else (stepAt tr tt q).ub))]
        else []) ∧
    rowTraffic WalkU.interactions tr tt q pub B_SEDGE sd =
      (if (stepAt tr tt q).mode = 4 then
        [Msg.toFp ((stepAt tr tt q).stubMsg (if sd then (stepAt tr tt q).u + 1 else (stepAt tr tt q).u))]
        else []) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, -⟩ := bus_ne
  obtain ⟨hsk, hb, -, ht⟩ := sk_iff hL hq ha
  have hm : (stepAt tr tt q).mode = modeOf tr tt q := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [rowT]
    simp only [n1.symm, n4, n5, false_and, if_false, List.nil_append, List.append_nil, true_and, hm]
    by_cases h : modeOf tr tt q ≤ 1
    · have hT := mT0 hL hq ha (by omega)
      rw [if_pos h, cellsE_eq hT]
      cases sd <;> simp [hsk.2 h, stepAt, Fp.ofNat_toNat, ofNat_succ]
    · rw [if_neg h]; have h' : ¬ tr.cell tt q mS + tr.cell tt q mK = 1 := fun e => h (hsk.1 e)
      cases sd <;> simp [h']
  · rw [rowT]
    simp only [n2.symm, n4.symm, n6, false_and, if_false, List.nil_append, List.append_nil, true_and, hm]
    by_cases h : modeOf tr tt q = 2
    · rw [if_pos h, cellsB_eq hL hq]
      cases sd <;> simp [hb.2 h, stepAt, Fp.ofNat_toNat, ofNat_succ]
    · rw [if_neg h]; have h' : ¬ tr.cell tt q mB = 1 := fun e => h (hb.1 e)
      cases sd <;> simp [h']
  · rw [rowT]
    simp only [n3.symm, n5.symm, n6.symm, false_and, if_false, List.nil_append, List.append_nil, true_and, hm]
    by_cases h : modeOf tr tt q = 4
    · rw [if_pos h, cellsS_eq hL hq (ht.2 h)]
      cases sd <;> simp [ht.2 h, stepAt, Fp.ofNat_toNat, ofNat_succ]
    · rw [if_neg h]; have h' : ¬ tr.cell tt q mT = 1 := fun e => h (ht.1 e)
      cases sd <;> simp [h']

end ZkFormal.NearV3.D1.WalkUProof

namespace ZkFormal.NearV3.D1.WalkUProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3 ZkFormal.NearV3.WalkV3
  ZkFormal.NearV3.D1.WalkU

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem walkUSends_one (wv : WalkR) (b : Nat) :
    walkUSends [wv] b =
      if b = B_EDGE then (wv.steps.filter fun st => st.mode ≤ 1).map fun st => st.edgeMsg (st.u + 1)
      else if b = ZkFormal.NearV3.B_BMAP then (wv.steps.filter fun st => st.mode = 2).map fun st => st.bmapMsg (st.ub + 1)
      else if b = B_SEDGE then (wv.steps.filter fun st => st.mode = 4).map fun st => st.stubMsg (st.u + 1)
      else [] := by
  obtain ⟨-, -, -, n4, n5, n6, -⟩ := bus_ne
  unfold walkUSends walkSends3
  by_cases h1 : b = B_EDGE
  · subst h1; simp
  · by_cases h2 : b = ZkFormal.NearV3.B_BMAP
    · subst h2; simp [n4.symm]
    · by_cases h3 : b = B_SEDGE
      · subst h3; simp [n5.symm, n6.symm]
      · simp [h1, h2, h3]

theorem walkURecvs_one (wv : WalkR) (b : Nat) :
    walkURecvs [wv] b =
      if b = B_EDGE then (wv.steps.filter fun st => st.mode ≤ 1).map fun st => st.edgeMsg st.u
      else if b = ZkFormal.NearV3.B_BMAP then (wv.steps.filter fun st => st.mode = 2).map fun st => st.bmapMsg st.ub
      else if b = B_SEDGE then (wv.steps.filter fun st => st.mode = 4).map fun st => st.stubMsg st.u
      else if b = B_UKEYNIB then walkRecvs3 [wv] B_KEYNIB
      else [] := by
  obtain ⟨n1, n2, n3, n4, n5, n6, -⟩ := bus_ne
  unfold walkURecvs walkRecvs3
  by_cases h1 : b = B_EDGE
  · subst h1; simp
  · by_cases h2 : b = ZkFormal.NearV3.B_BMAP
    · subst h2; simp [n4.symm]
    · by_cases h3 : b = B_SEDGE
      · subst h3; simp [n5.symm, n6.symm]
      · by_cases h4 : b = B_UKEYNIB
        · subst h4; simp [n1, n2, n3]
        · simp [h1, h2, h3, h4]

theorem segTraffic (hL : TableLocal WalkU.table tr tt pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt ws) (isOne tr tt we) s ℓ) (hH : s + ℓ ≤ tr.height tt)
    (b : Nat) (sd : Bool) :
    (List.range' s ℓ).flatMap (fun q => rowTraffic WalkU.interactions tr tt q pub b sd) =
      ((if sd then walkUSends else walkURecvs) [walkOfSeg tr tt (s, ℓ)] b).map Msg.toFp := by
  obtain ⟨h2, hrow, -, -, -, -⟩ := segInfo hL hseg hH
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := bus_ne
  have hR := fun j (hj : j < ℓ) => rowMode hL (q := s + j) (by omega) (hrow j hj).1 sd
  by_cases hE : b = B_EDGE
  · subst hE
    rw [segStep hL hseg hH _ sd n1.symm (fun m => decide (m ≤ 1))
      (fun st => st.edgeMsg (if sd then st.u + 1 else st.u)) (fun j hj => by simpa using (hR j hj).1)]
    cases sd <;> simp [walkUSends_one, walkURecvs_one]
  · by_cases hB : b = ZkFormal.NearV3.B_BMAP
    · subst hB
      rw [segStep hL hseg hH _ sd n2.symm (fun m => decide (m = 2))
        (fun st => st.bmapMsg (if sd then st.ub + 1 else st.ub)) (fun j hj => by simpa using (hR j hj).2.1)]
      cases sd <;> simp [walkUSends_one, walkURecvs_one, n4.symm]
    · by_cases hS : b = B_SEDGE
      · subst hS
        rw [segStep hL hseg hH _ sd n3.symm (fun m => decide (m = 4))
          (fun st => st.stubMsg (if sd then st.u + 1 else st.u)) (fun j hj => by simpa using (hR j hj).2.2)]
        cases sd <;> simp [walkUSends_one, walkURecvs_one, n5.symm, n6.symm]
      · by_cases hK : b = B_UKEYNIB ∧ sd = false
        · obtain ⟨rfl, rfl⟩ := hK
          simp only [Bool.false_eq_true, if_false]
          rw [walkURecvs_one, if_neg n1, if_neg n2, if_neg n3, if_pos rfl]
          simp only [walkRecvs3, if_neg (show B_KEYNIB ≠ B_EDGE by decide),
            if_neg (show B_KEYNIB ≠ ZkFormal.NearV3.B_BMAP by decide), if_pos rfl, walkOfSeg,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map, List.length_range]
          have hs : List.range' s ℓ = [s] ++ List.range' (s + 1) (ℓ - 1) := by
            rw [show ℓ = 1 + (ℓ - 1) by omega, ← List.range'_append_1]; simp
          rw [hs, List.flatMap_append]
          have h0 := hrow 0 (by omega)
          rw [Nat.add_zero] at h0
          rw [List.flatMap_singleton, rowT, h0.2.2.2.2.1]
          simp only [if_pos rfl, ↓reduceIte, fp_zero_ne_one, and_false, if_false, n1, n2, n3, false_and,
            List.nil_append, List.append_nil]
          rw [flatMap_range'_single _ (fun j => [tr.cell tt (s + 1 + j) w, tr.cell tt (s + 1 + j) t,
            tr.cell tt (s + 1 + j) sym, tr.cell tt (s + 1 + j) we]) (s + 1) (ℓ - 1) (fun j hj => by
              have := hrow (j + 1) (by have := h2; omega)
              rw [show s + (j + 1) = s + 1 + j by omega] at this
              rw [rowT, this.2.2.2.2.1, if_neg (Nat.succ_ne_zero j)]; simp [n1, n2, n3])]
          try simp only [List.map_map]
          apply List.map_congr_left; intro j hj
          rw [List.mem_range] at hj
          have := hrow (j + 1) (by omega)
          rw [show s + (j + 1) = s + 1 + j by omega] at this
          obtain ⟨-, hr, -, hw, -, ht⟩ := this
          simp only [Function.comp, Msg.toFp, List.map_cons, List.map_nil, WalkR.step, List.getD_eq_getElem?_getD,
            List.getElem?_map, List.getElem?_range (show j + 1 < ℓ by omega), Option.map_some, Option.getD_some,
            stepAt, Fp.ofNat_toNat]
          rw [hr, hw, ht (by omega), ite01]
          simp [show j + 1 - 1 = j by omega, show s + (j + 1) = s + 1 + j by omega, natCast_eq,
            show (j + 1 + 1 = ℓ) ↔ (j + 2 = ℓ) by omega]
        · rw [flatMap_range'_nil _ _ _ (fun j _ => by
            rw [rowT]; cases sd <;> simp_all)]
          cases sd <;> simp_all [walkUSends_one, walkURecvs_one]

end ZkFormal.NearV3.D1.WalkUProof

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 WalkUProof

theorem walkSends3_flat' (ws : List WalkR) (b : Nat) :
    walkSends3 ws b = ws.flatMap fun w => walkSends3 [w] b := by
  unfold walkSends3; split
  · simp
  · split
    · simp
    · split
      · simp [map_eq_flatMap]
      · simp

theorem walkRecvs3_flat' (ws : List WalkR) (b : Nat) :
    walkRecvs3 ws b = ws.flatMap fun w => walkRecvs3 [w] b := by
  unfold walkRecvs3; split
  · simp
  · split
    · simp
    · split <;> simp

theorem walkUSends_flat (ws : List WalkR) (b : Nat) :
    walkUSends ws b = ws.flatMap fun w => walkUSends [w] b := by
  unfold walkUSends; split
  · rw [walkSends3_flat']; try simp
  · split <;> simp

theorem walkURecvs_flat (ws : List WalkR) (b : Nat) :
    walkURecvs ws b = ws.flatMap fun w => walkURecvs [w] b := by
  unfold walkURecvs; split
  · rw [walkRecvs3_flat']; try simp
  · split
    · simp
    · split
      · rw [walkRecvs3_flat']; try simp
      · simp

/-- **The `walkU` view.** -/
theorem walkU_view : WalkUViewStmt := by
  intro tr pub tt hL
  obtain ⟨segs, hc, hend, hall, hpad⟩ := segments_of (segFacts hL) height_pos
  have hH : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height tt := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  have hpadT : ∀ b sd, ∀ q, segEnd 0 segs ≤ q → q < tr.height tt →
      rowTraffic WalkU.interactions tr tt q pub b sd = [] := by
    intro b sd q h1 h2
    have h0 := zero_of_not_one hL h2 bc_act (hpad q h1 h2)
    have hm := (rowFacts hL h2).2.1
    rw [h0] at hm
    have b1 := isBool hL h2 bc_mS; have b2 := isBool hL h2 bc_mK
    have b3 := isBool hL h2 bc_mB; have b4 := isBool hL h2 bc_mD; have b5 := isBool hL h2 bc_mT
    have hz : tr.cell tt q WalkV3.mS = 0 ∧ tr.cell tt q WalkV3.mK = 0 ∧ tr.cell tt q WalkV3.mB = 0 ∧
        tr.cell tt q WalkU.mT = 0 := by
      rcases b1 with h1 | h1 <;> rcases b2 with h2 | h2 <;> rcases b3 with h3 | h3 <;>
        rcases b4 with h4 | h4 <;> rcases b5 with h5 | h5 <;> rw [h1, h2, h3, h4, h5] at hm <;>
        first | (exfalso; revert hm; decide) | exact ⟨h1, h2, h3, h5⟩
    have hg : tr.cell tt q WalkV3.gK = 0 := by
      rw [(rowFacts hL h2).1, h0]
      rcases isBool hL h2 bc_ws with h | h
      · rw [h]; grind
      · have := ((rowFacts hL h2).2.2.1 h).1; rw [h0] at this; exact absurd this (by decide)
    rw [rowT]
    simp [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2, hg, show (0 : Fp) + 0 = 0 by grind]
  have hrows : ((segs.map (walkOfSeg tr tt)).flatMap (·.steps)).length ≤ 2 ^ 22 := by
    have hl := congrArg List.length (range'_segs segs 0 hc)
    simp only [List.length_range', Nat.sub_zero, List.length_flatMap] at hl
    have hle := height_le hL
    rw [List.flatMap_map, List.length_flatMap]
    simp only [walkOfSeg, List.length_map, List.length_range]
    omega
  refine ⟨segs.map (walkOfSeg tr tt), ⟨?_, ?_, ?_, ?_, ?_, hrows⟩, fun b m => ⟨?_, ?_⟩⟩
  · intro wv hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    obtain ⟨h2, -⟩ := segInfo hL (hall p hp) (hH p hp)
    simp [walkOfSeg]; omega
  · intro wv hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    refine ⟨Fp.toNat_lt _, Fp.toNat_lt _, fun st hst => ?_⟩
    simp only [walkOfSeg, List.mem_map, List.mem_range] at hst
    obtain ⟨j, -, rfl⟩ := hst
    refine ⟨Fp.toNat_lt _, Fp.toNat_lt _, Fp.toNat_lt _, fun x hx => ?_⟩
    simp only [stepAt, edgeAt, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact Fp.toNat_lt _ | skip
    simp only [zAt]
    split
    · split
      · simp [SYM_WILD, P]
      · exact Fp.toNat_lt _
    · exact Fp.toNat_lt _
  · intro wv hw i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    obtain ⟨h2, hrow, -⟩ := segInfo hL (hall p hp) (hH p hp)
    simp only [walkOfSeg, List.length_map, List.length_range] at hi ⊢
    simp only [List.getElem_map, List.getElem_range]
    apply stepOk hL (by have := hH p hp; omega) (hrow i hi).1
    rw [(hrow i hi).2.2.2.1]
    by_cases h : i + 1 = p.2 <;> simp [h]
  · intro wv hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    obtain ⟨h2, -, hS, hI, hsym, -⟩ := segInfo hL (hall p hp) (hH p hp)
    have hws : tr.cell tt p.1 WalkV3.ws = 1 := by
      have := (hall p hp).2.1; simpa [isOne] using this
    have htau := ((rowFacts hL (by have := hH p hp; omega)).2.2.1 hws).2.2.2.2.2.2
    have hT0 := mT0 hL (q := p.1) (by have := hH p hp; omega) ((rowFacts hL
      (by have := hH p hp; omega)).2.2.1 hws).1 (by simp [modeOf, hS])
    simp only [walkOfSeg, WalkR.step, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show 0 < p.2 by omega), Option.map_some, Option.getD_some, Nat.add_zero]
    refine ⟨by simp [stepAt, modeOf, hS], by simp [stepAt, hsym, natCast_eq, Fp.toNat_ofNat, SYM_START, P],
      by simp [stepAt, edgeAt, hI], by simp [htau]; rfl⟩
  · intro wv hw i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    obtain ⟨-, hrow, -, -, -, hch⟩ := segInfo hL (hall p hp) (hH p hp)
    simp only [walkOfSeg, List.length_map, List.length_range] at hi
    have hc := hch i hi
    have hq : p.1 + i < tr.height tt := by have := hH p hp; omega
    simp only [walkOfSeg, WalkR.step, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi, List.getElem?_range (show i < p.2 by omega), Option.map_some, Option.getD_some]
    have e : p.1 + (i + 1) = p.1 + i + 1 := by omega
    rw [e]
    have ha1 := (hrow (i + 1) hi).1; rw [e] at ha1
    have hq1 : p.1 + i + 1 < tr.height tt := by have := hH p hp; omega
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · have hs1 := mode0 hm
      obtain ⟨hN, hI, hD⟩ := hc.1 hs1
      have hT := mT0 hL hq1 ha1
      refine ⟨by simp [stepAt, edgeAt, hN, hI], ?_⟩
      intro h3
      change modeOf tr tt (p.1 + i + 1) = 3 at h3
      rcases modes_cases (q := p.1 + i + 1) hL hq1 ha1 with h | h | h | h | h <;>
        simp [modeOf, h] at h3
      rw [hD] at h; exact absurd h.2.2.2.1 (by decide)
    · have hs0 : tr.cell tt (p.1 + i) WalkV3.mS = 0 := by
        rcases isBool hL hq bc_mS with h | h
        · exact h
        · exact absurd (by simp [stepAt, modeOf, h]) hm
      have hD := hc.2 hs0
      rcases modes_cases (q := p.1 + i + 1) hL hq1 ha1 with h | h | h | h | h <;>
        simp [stepAt, modeOf, h] at hD ⊢
  · simp only [walkUTraffic]
    rw [tableBusCount_eq, flatMap_rows_segs _ segs _ hc hend (hpadT b true),
      flatMap_segs segs _ _ (fun p hp => segTraffic hL (hall p hp) (hH p hp) b true), walkUSends_flat]
    simp [List.map_flatMap, walkOfSeg, List.flatMap_map]
  · simp only [walkUTraffic]
    rw [tableBusCount_eq, flatMap_rows_segs _ segs _ hc hend (hpadT b false),
      flatMap_segs segs _ _ (fun p hp => segTraffic hL (hall p hp) (hH p hp) b false), walkURecvs_flat]
    simp [List.map_flatMap, walkOfSeg, List.flatMap_map]

end ZkFormal.NearV3.D1
