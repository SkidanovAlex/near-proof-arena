import ZkFormal.NearV3.D1.Extract.Akm.Traffic

/-!
# `ZkFormal.NearV3.D1.Extract.Akm.Lane` — one row of a segment: its traffic as naturals
-/

namespace ZkFormal.NearV3.D1.AkmProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.AkmV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem cvOne {r x : Nat} : cv tr tt r x = 1 ↔ tr.cell tt r x = 1 := by
  constructor
  · intro h; rw [cell_eq_cast, h]; rfl
  · intro h; unfold cv; rw [h]; rfl

section
variable (hL : TableLocal AkmV3.table tr tt pub)
include hL

theorem memc {r : Nat} (hr : r < tr.height tt) {g x y : Nat} (hm : sub (c g) (.mul (c x) (c y)) ∈ cMem) :
    tr.cell tt r g = tr.cell tt r x * tr.cell tt r y := by
  have := con hL hr (mem_mem hm); simp only [eval_sub, eval_mul, eval_c] at this; grind

/-- **One row's traffic** in a segment. -/
theorem rowLaneA {s ℓ : Nat} (seg : SegAt tr tt s ℓ) (j : Nat) (hj : j < ℓ) (bb : Nat) (sd : Bool) :
    rowTraffic AkmV3.interactions tr tt (s + j) pub bb sd = (rowMsgsA (akmOf tr tt s ℓ) j bb sd).map Msg.toFp := by
  have hH := seg.h
  have hr : s + j < tr.height tt := by omega
  obtain ⟨k, -, -, -, hfa, h9, hnon, hnoN, hT8⟩ := akm_decode hL seg
  have ha := seg.act j hj
  have hpos := seg.posv j hj
  have haf := seg.af j hj
  have cst := fun x (hx : x ∈ segConst) => seg.const j hj x hx
  have hvid := cst vid (by simp [segConst]); have ht1 := cst (t 1) (by simp [segConst])
  have htl := cst tlast (by simp [segConst]); have hU := cst U (by simp [segConst])
  have hsN : tr.cell tt (s + j) sN = if j < 8 then 1 else 0 := by
    split
    · exact (hnon j (by omega)).1
    · exact hnoN j (by omega) hj
  have tb := isBool hL (by omega : s < tr.height tt) (t_bool hL 1 (by omega))
  have haF := memc hL hr (g := aF) (x := af) (y := t 1) (by simp [cMem])
  have hnF := memc hL hr (g := nF) (x := sN) (y := t 1) (by simp [cMem])
  have htF := memc hL hr (g := tF) (x := sT) (y := t 1) (by simp [cMem])
  rw [ht1] at haF hnF htF
  have htF' : tr.cell tt (s + j) tF = if j = 8 then tr.cell tt s (t 1) else 0 := by
    rcases tb with h0 | h1
    · rw [htF, h0]; split <;> grind
    · obtain ⟨hl9, -⟩ := hfa h1
      by_cases h8 : j = 8
      · subst h8; rw [htF, hT8]; simp only [ite_true]; grind
      · have hN := (hnon j (by omega)).1
        have hT0 := oneHot hL hr ha (by simp [states]) hN sT (by simp [states]) (by decide)
        rw [htF, hT0, if_neg h8]; grind
  have hbE := eval_bE hL hr (pub := pub)
  have bl := bvA_lt hL hr
  have hgb : (akmOf tr tt s ℓ).bytes.getD j 0 = bvA tr tt (s + j) := by
    simp [akmOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  have hgp : j < 8 → (akmOf tr tt s ℓ).pb.getD j 0 = cv tr tt (s + j) pb := fun h8 => by
    simp [akmOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h8]
  have im : ∀ {C D : Prop} [Decidable C] [Decidable D] (m : Msg) (v : List Fp), (C ↔ D) →
      (D → Msg.toFp m = v) → (if C then [v] else []) = (if D then [m] else []).map Msg.toFp := by
    intro C D _ _ m v hCD h
    by_cases hD : D
    · rw [if_pos (hCD.mpr hD), if_pos hD]; simp [h hD]
    · rw [if_neg (fun hC => hD (hCD.mp hC)), if_neg hD]; rfl
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  have ecv : ∀ x, Fp.ofNat (cv tr tt s x) = tr.cell tt s x := fun x => ofNat_cv tr tt s x
  have i1 : ∀ (x : Fp), (x = 1 ↔ cv tr tt s (t 1) = 1) → ((if j = 0 then (1 : Fp) else 0) * x = 1 ↔
      (j = 0 ∧ (akmOf tr tt s ℓ).fa = 1)) := by
    intro x hx
    by_cases h : j = 0
    · subst h; simp only [ite_true, true_and, akmOf]; rw [← hx]; constructor <;> intro h' <;> grind
    · simp only [h, ite_false, false_and, iff_false]; intro h'; exact fp_zero_ne_one (by grind)
  have fa1 : tr.cell tt s (t 1) = 1 ↔ cv tr tt s (t 1) = 1 := cvOne.symm
  rw [haf] at haF
  have evp : Fp.ofNat (K_VPOST + 16 * cv tr tt s vid) = ((K_VPOST : Nat) : Fp) + ((16 : Nat) : Fp) * tr.cell tt s vid := by
    rw [← ofNat_add', ← ofNat_mul', ofNat_cv]; rfl
  rw [rowT, ha, hpos, hnF, hsN, haF, htF', hbE, hvid, ht1, htl, hU]
  unfold rowMsgsA
  cases sd
  · simp only [Bool.false_eq_true, ite_false, and_false, false_and, List.append_nil, List.nil_append,
      List.map_append, and_true, true_and]
    refine ap ?_ ?_
    · refine im _ _ ?_ (fun h => ?_)
      · by_cases h8 : j < 8 <;> simp [h8, fp_zero_ne_one]
      · rw [hgp h.2, (hnon j h.2).2]; simp [Msg.toFp, akmOf, ecv, ofNat_cv, natCast_eq]
    · refine im _ _ ?_ (fun _ => ?_)
      · rw [and_congr_right_iff]; intro; exact i1 _ fa1
      · simp [Msg.toFp, akmOf, ecv, natCast_eq]
  · simp only [ite_true, and_false, false_and, ite_false, List.nil_append, List.append_nil, List.map_append,
      and_true, true_and, Bool.true_eq_false]
    refine ap (ap (ap (ap (ap ?_ ?_) ?_) ?_) ?_) ?_
    · refine im _ _ ?_ (fun _ => ?_)
      · simp
      · rw [hgb]; simp [Msg.toFp, akmOf, ecv, natCast_eq]
    · refine im _ _ ?_ (fun h => ?_)
      · by_cases h8 : j < 8 <;> simp [h8, fp_zero_ne_one]
      · rw [hgb, (hnon j h.2).2]; simp [Msg.toFp, akmOf, ecv, natCast_eq]
    · refine im _ _ ?_ (fun _ => ?_)
      · rw [and_congr_right_iff]; intro; exact i1 _ fa1
      · simp [Msg.toFp, akmOf, ecv, natCast_eq]
    · refine im _ _ ?_ (fun h => ?_)
      · rw [and_congr_right_iff]; intro
        by_cases h8 : j < 8
        · simp only [h8, ite_true, true_and, akmOf]; rw [← fa1]; constructor <;> intro h' <;> grind
        · simp only [h8, ite_false, false_and, iff_false]; intro h'; exact fp_zero_ne_one (by grind)
      · rw [hgp h.2.1]
        simp only [Msg.toFp, akmOf, AkmE.vpost, List.map_cons, List.map_nil, evp, ofNat_cv, natCast_eq]
    · refine im _ _ ?_ (fun h => ?_)
      · rw [and_congr_right_iff]; intro
        by_cases h8 : j = 8 <;> simp [h8, fp_zero_ne_one, akmOf, ← fa1]
      · obtain ⟨-, rfl, -⟩ := h
        rw [hgb]
        simp only [Msg.toFp, akmOf, AkmE.vpost, List.map_cons, List.map_nil, evp, ofNat_cv, natCast_eq]
    · refine im _ _ ?_ (fun _ => ?_)
      · rw [and_congr_right_iff]; intro; exact i1 _ fa1
      · simp [Msg.toFp, akmOf, ecv, natCast_eq]

end

end ZkFormal.NearV3.D1.AkmProof
