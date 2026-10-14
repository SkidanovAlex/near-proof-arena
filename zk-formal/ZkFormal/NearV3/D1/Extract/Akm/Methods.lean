import ZkFormal.NearV3.D1.Extract.Akm.Str

/-!
# `ZkFormal.NearV3.D1.Extract.Akm.Methods` — the method-name list of a function-call permission

After the receiver string (`mth = 0`): the `u32` count `v`, then `v` method-name strings
(`mth = 1`); the segment ends exactly after the last one (or after a zero count).
`pVec "method_names" (pString "method_name")` reads exactly that.
-/

namespace ZkFormal.NearV3.D1.AkmProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.AkmV3 NearSpecV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

section
variable (hL : TableLocal AkmV3.table tr tt pub)
include hL

theorem seg_end {s ℓ : Nat} (seg : SegAt tr tt s ℓ) {p : Nat} (hp : p < ℓ) (hal : tr.cell tt (s + p) al = 1) :
    p + 1 = ℓ := by
  have := seg.al p hp; rw [hal] at this
  by_cases h : p + 1 = ℓ
  · exact h
  · rw [if_neg h] at this; exact absurd this fp_one_ne_zero

/-- A row with no accepting event does not end the segment. -/
theorem al0 {s ℓ : Nat} (seg : SegAt tr tt s ℓ) {p : Nat} (hp : p < ℓ)
    (hT : tr.cell tt (s + p) sT = 0) (hG : tr.cell tt (s + p) sG = 0) (hC : tr.cell tt (s + p) sC = 0)
    (hmd : tr.cell tt (s + p) md = 0) : tr.cell tt (s + p) al = 0 := by
  have hr : s + p < tr.height tt := by have := seg.h; omega
  rw [al_endOK hL hr (seg.act p hp), endOK_eq hL hr, hT, hG, hC, hmd]; grind

/-- The end of the receiver string goes to the count field. -/
theorem rcv_to_count {s ℓ q e : Nat} (seg : SegAt tr tt s ℓ) (E : StrEnd tr tt s ℓ q e)
    (hm : tr.cell tt (s + q) mth = 0) : FStart tr tt s ℓ e sC := by
  have hH := seg.h
  obtain ⟨⟨he1, he2⟩, hsd, hfe, hmth, ⟨_, hT, hG, hC⟩, -, -⟩ := E
  have hp : e - 1 < ℓ := by omega
  have hr : s + (e - 1) < tr.height tt := by omega
  rw [hm] at hmth
  have hmd : tr.cell tt (s + (e - 1)) md = 0 := by rw [md_eq hL hr, hmth]; grind
  have hal := al0 hL seg hp hT hG hC hmd
  have hn := seg_next hL seg hp hal
  have hr1 : s + (e - 1) + 1 < tr.height tt := by omega
  obtain ⟨hgo, hix⟩ := fgo_next hL hr1 hfe hal
  have hC1 := transGo hL hr1 hal (a := c sd) (b := not (c mth)) (x := sC) (by simp [cEvents])
    (by simp only [eval_c]; exact hsd) (by simp only [eval_not, eval_c, hmth]; grind)
  rw [show s + (e - 1) + 1 = s + e by omega] at hC1 hix
  exact ⟨by omega, by omega, hC1, hix, by rw [show s + e - 1 = s + (e - 1) by omega]; exact hgo⟩

/-- **The method names**: `v ≥ 1` strings, the segment ends after the last. -/
theorem methods {s ℓ : Nat} (seg : SegAt tr tt s ℓ) : ∀ v q, 1 ≤ v → v < 16777216 →
    FStart tr tt s ℓ q sL → tr.cell tt (s + q) mth = 1 → tr.cell tt (s + q) vc = ((v : Nat) : Fp) →
    ∃ ms, pMany (pString "method_name") v (win (segF tr tt s) q (ℓ - q)) =
      .ok (ms, win (segF tr tt s) ℓ (ℓ - ℓ)) ∧ ∀ j, q ≤ j → j < ℓ → tr.cell tt (s + j) sN = 0 := by
  have hH := seg.h
  intro v
  induction v with
  | zero => intro _ h; omega
  | succ v ih =>
    intro q hv hvP hq hm hvc
    obtain ⟨e, E, hp⟩ := str hL seg hq "method_name"
    obtain ⟨⟨he1, he2⟩, hsd, hfe, hmth, ⟨_, hT, hG, hC⟩, hvce, hnoN⟩ := E
    have hpe : e - 1 < ℓ := by omega
    have hr : s + (e - 1) < tr.height tt := by omega
    rw [hm] at hmth; rw [hvc] at hvce
    have hmd : tr.cell tt (s + (e - 1)) md = 1 := by rw [md_eq hL hr, hmth, hsd]; grind
    obtain ⟨hzb, hziff⟩ := zV_iff hL hr hmd
    simp only [pMany, bind, Except.bind, hp]
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · -- the last method
      subst h0
      have hz : tr.cell tt (s + (e - 1)) zV = 1 := hziff.mpr (by rw [hvce]; rfl)
      have hal : tr.cell tt (s + (e - 1)) al = 1 := by
        rw [al_endOK hL hr (seg.act (e - 1) hpe), endOK_eq hL hr, hT, hG, hC, hmd, hz]; grind
      have hee := seg_end hL seg hpe hal
      refine ⟨_, by rw [show e = ℓ by omega]; rfl, fun j h1 h2 => hnoN j h1 (by omega)⟩
    · -- more methods follow
      have hz : tr.cell tt (s + (e - 1)) zV = 0 := by
        rcases hzb with hz | hz
        · exact hz
        · exfalso
          have h1 := hziff.mp hz; rw [hvce] at h1
          have := ofNat_inj (a := v + 1) (b := 1) (by unfold ZkFormal.Algebra.P; omega)
            (by unfold ZkFormal.Algebra.P; omega) h1
          omega
      have hal : tr.cell tt (s + (e - 1)) al = 0 := by
        rw [al_endOK hL hr (seg.act (e - 1) hpe), endOK_eq hL hr, hT, hG, hC, hmd, hz]; grind
      have hn := seg_next hL seg hpe hal
      have hr1 : s + (e - 1) + 1 < tr.height tt := by omega
      obtain ⟨hgo, hix⟩ := fgo_next hL hr1 hfe hal
      have heM : tr.cell tt (s + (e - 1)) eM = 1 := by rw [eM_eq hL hr, hmd, hz]; grind
      have hL1 := trans1 hL hr1 (g := c eM) (x := sL) (by simp [cEvents]) (by simp only [eval_c]; exact heM)
      have hm1 := trans1 hL hr1 (g := c eM) (x := mth) (by simp [cEvents]) (by simp only [eval_c]; exact heM)
      have heC : tr.cell tt (s + (e - 1)) eC = 0 := by rw [eC_eq hL hr, hC]; grind
      have hv1 := vc_step hL hr1 (seg.act (e - 1) hpe) hal
      rw [hvce, hmd, heC] at hv1
      rw [show s + (e - 1) + 1 = s + e by omega] at hL1 hm1 hix hv1
      obtain ⟨ms, hms, hnoN'⟩ := ih e (by omega) (by omega)
        ⟨by omega, by omega, hL1, hix, by rw [show s + e - 1 = s + (e - 1) by omega]; exact hgo⟩ hm1
        (by rw [hv1, natCast_add]; grind)
      rw [hms]
      refine ⟨_, rfl, fun j h1 h2 => ?_⟩
      by_cases hj : j < e
      · exact hnoN j h1 hj
      · exact hnoN' j (by omega) h2

/-- **The count and the method names**: `pVec` reads up to the segment end. -/
theorem vecMethods {s ℓ c : Nat} (seg : SegAt tr tt s ℓ) (hc : FStart tr tt s ℓ c sC) :
    ∃ ms, pVec "method_names" (pString "method_name") (win (segF tr tt s) c (ℓ - c)) =
      .ok (ms, win (segF tr tt s) ℓ (ℓ - ℓ)) ∧ ∀ j, c ≤ j → j < ℓ → tr.cell tt (s + j) sN = 0 := by
  have hH := seg.h
  obtain ⟨hcl, hc1, hst, hix, hgo⟩ := hc
  obtain ⟨hp3, hfe3, hb3, hacc, hzb, hziff⟩ := u32field hL seg (Or.inr rfl) hcl hc1 hst hix hgo
  have F := field hL seg (x := sC) (L := 3) (by simp [FixedLen]) hcl hst hix
  obtain ⟨v, hv⟩ : ∃ v, v = bvA tr tt (s + c) + 256 * bvA tr tt (s + c + 1) + 65536 * bvA tr tt (s + c + 2) :=
    ⟨_, rfl⟩
  rw [← hv] at hacc hziff
  have bl := fun j (hj : j ≤ 3) => bvA_lt hL (r := s + c + j) (by have := (F j hj).1; omega)
  have hvP : v < 16777216 := by
    have := bl 0 (by omega); have := bl 1 (by omega); have := bl 2 (by omega); simp only [Nat.add_zero] at *
    omega
  have hwv : winVal (segF tr tt s) c 4 = v := by
    rw [winVal_four]; simp only [segF]
    rw [u8b hL (by omega), u8b hL (by omega), u8b hL (by omega), u8b hL (by omega)]
    simp only [← Nat.add_assoc, hb3]; omega
  have hr3 : s + c + 3 < tr.height tt := by omega
  have ha3 : tr.cell tt (s + c + 3) act = 1 := by have := seg.act (c + 3) hp3; rwa [← Nat.add_assoc] at this
  have noC : ∀ j, c ≤ j → j < c + 4 → tr.cell tt (s + j) sN = 0 := by
    intro j h1 h2
    have := (F (j - c) (by omega)).2.1
    rw [show s + c + (j - c) = s + j by omega] at this
    exact notN hL (by omega) (by have := seg.act j (by omega); exact this) (by simp [states]) (by decide) this
  have st3 := (F 3 (by omega)).2.1
  have z := oneHot hL hr3 ha3 (by simp [states]) st3
  have hT := z sT (by simp [states]) (by decide); have hG := z sG (by simp [states]) (by decide)
  have hLz := z sL (by simp [states]) (by decide); have hSz := z sS (by simp [states]) (by decide)
  have hsd : tr.cell tt (s + c + 3) sd = 0 := by rw [sd_eq hL hr3, hLz, hSz]; grind
  have hmd : tr.cell tt (s + c + 3) md = 0 := by rw [md_eq hL hr3, hsd]; grind
  simp only [pVec, bind, Except.bind]
  rw [pU32_win (segF tr tt s) c (ℓ - c) (by omega), hwv]
  simp only
  rcases hzb with hz | hz
  · have hv0 : v ≠ 0 := fun h => by rw [hziff.mpr h] at hz; exact fp_zero_ne_one hz.symm
    have hal : tr.cell tt (s + c + 3) al = 0 := by
      rw [al_endOK hL hr3 ha3, endOK_eq hL hr3, hT, hG, hmd, hz]; grind
    have hn := seg_next hL seg (p := c + 3) hp3 (by rw [← Nat.add_assoc]; exact hal)
    have hr4 : s + c + 3 + 1 < tr.height tt := by omega
    obtain ⟨hgo3, hix4⟩ := fgo_next hL hr4 hfe3 hal
    have heC : tr.cell tt (s + c + 3) eC = 1 := by rw [eC_eq hL hr3, st3, hgo3, hz]; grind
    have hL4 := trans1 hL hr4 (g := Dsl.c eC) (x := sL) (by simp [cEvents]) (by simp only [eval_c]; exact heC)
    have hm4 := trans1 hL hr4 (g := Dsl.c eC) (x := mth) (by simp [cEvents]) (by simp only [eval_c]; exact heC)
    have hv4 := vc_step hL hr4 ha3 hal
    rw [hmd, heC, hacc] at hv4
    rw [show s + c + 3 + 1 = s + (c + 4) by omega] at hL4 hm4 hix4 hv4
    obtain ⟨ms, hms, hnoN⟩ := methods hL seg v (c + 4) (by omega) hvP
      ⟨by omega, by omega, hL4, hix4, by rw [show s + (c + 4) - 1 = s + c + 3 by omega]; exact hgo3⟩ hm4
      (by rw [hv4]; grind)
    rw [show ℓ - c - 4 = ℓ - (c + 4) by omega, hms]
    refine ⟨_, rfl, fun j h1 h2 => ?_⟩
    by_cases hj : j < c + 4
    · exact noC j h1 hj
    · exact hnoN j (by omega) h2
  · have hv0 : v = 0 := hziff.mp hz
    have hal : tr.cell tt (s + c + 3) al = 1 := by
      rw [al_endOK hL hr3 ha3, endOK_eq hL hr3, hT, hG, hmd, hz, st3, hfe3]; grind
    have hee := seg_end hL seg (p := c + 3) hp3 (by rw [← Nat.add_assoc]; exact hal)
    rw [hv0]
    simp only [pMany, pure, Except.pure]
    rw [show c + 4 = ℓ by omega, show ℓ - c - 4 = ℓ - ℓ by omega]
    exact ⟨_, rfl, fun j h1 h2 => noC j h1 (by omega)⟩

end

end ZkFormal.NearV3.D1.AkmProof
