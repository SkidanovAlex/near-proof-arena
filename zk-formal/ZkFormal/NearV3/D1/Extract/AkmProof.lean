import ZkFormal.NearV3.D1.Extract.Akm.Lane

/-!
# `ZkFormal.NearV3.D1.Extract.AkmProof` — **the `akmV3` view** (`akm_view : AkmViewStmt`)

Lane `v3-d1-phase2` (milestone V3).  Statement: `Extract/AkmView.lean`.  The rows split into
value segments (`Akm.Rows.segInfo`); each segment's bytes decode as an access key
(`Akm.Decode.akm_decode`: the borsh walk `Akm.Field`/`Str`/`Methods`, UTF-8 `Akm.Utf8*`); its
traffic is `rowMsgsA` row by row (`Akm.Traffic`, `Akm.Lane`).
-/

namespace ZkFormal.NearV3.D1.AkmProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.AkmV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

section
variable (hL : TableLocal AkmV3.table tr tt pub)
include hL

/-- An inactive row carries no traffic. -/
theorem inactiveA {r : Nat} (hr : r < tr.height tt) (ha : tr.cell tt r act = 0) (bb : Nat) (sd : Bool) :
    rowTraffic AkmV3.interactions tr tt r pub bb sd = [] := by
  have haf := ((rowFacts hL hr).2.2 ha).1
  have e := con hL hr (mem_shape (e := sub (sum (states.map c)) (c act)) (by simp [cShape]))
  simp only [states, List.map_cons, List.map_nil, eval_sub, eval_sum_cons, eval_sum_nil, eval_c, ha] at e
  have b := fun y (hy : y ∈ states) => cv_bool (isBool hL hr (states_bool y hy))
  have hs : cv tr tt r sN + cv tr tt r sT + cv tr tt r sG + cv tr tt r sO + cv tr tt r sA +
      cv tr tt r sL + cv tr tt r sS + cv tr tt r sC = 0 := by
    have b1 := b sN (by simp [states]); have b2 := b sT (by simp [states])
    have b3 := b sG (by simp [states]); have b4 := b sO (by simp [states])
    have b5 := b sA (by simp [states]); have b6 := b sL (by simp [states])
    have b7 := b sS (by simp [states]); have b8 := b sC (by simp [states])
    apply ofNat_inj (by unfold ZkFormal.Algebra.P; omega) (by unfold ZkFormal.Algebra.P; omega)
    simp only [natCast_add, ← cell_eq_cast]
    rw [show ((0 : Nat) : Fp) = 0 from rfl]; grind
  have hN : tr.cell tt r sN = 0 := by rw [cell_eq_cast, show cv tr tt r sN = 0 by omega]; rfl
  have hT : tr.cell tt r sT = 0 := by rw [cell_eq_cast, show cv tr tt r sT = 0 by omega]; rfl
  have haF := memc hL hr (g := aF) (x := af) (y := t 1) (by simp [cMem])
  have hnF := memc hL hr (g := nF) (x := sN) (y := t 1) (by simp [cMem])
  have htF := memc hL hr (g := tF) (x := sT) (y := t 1) (by simp [cMem])
  rw [haf] at haF; rw [hN] at hnF; rw [hT] at htF
  rw [rowT, ha, hN, show tr.cell tt r aF = 0 by grind, show tr.cell tt r nF = 0 by grind,
    show tr.cell tt r tF = 0 by grind]
  simp [fp_zero_ne_one]

/-- The facts of one segment. -/
theorem segWf {s ℓ : Nat} (seg : SegAt tr tt s ℓ) : AkmSegWf (akmOf tr tt s ℓ) := by
  have hH := seg.h
  obtain ⟨k, hk, hn, hfa, hfa1, h9, hnon, -, -⟩ := akm_decode hL seg
  have hr0 : s < tr.height tt := by omega
  have hwin : win (segF tr tt s) 0 ℓ = (akmOf tr tt s ℓ).bytes.map UInt8.ofNat := by
    simp [win, segF, akmOf, List.range_eq_range', Function.comp_def]
  have hwin8 : win (segF tr tt s) 0 8 = ((akmOf tr tt s ℓ).bytes.take 8).map UInt8.ofNat := by
    rw [show (akmOf tr tt s ℓ).bytes.take 8 = (List.range 8).map fun j => bvA tr tt (s + j) by
      simp only [akmOf, ← List.map_take, List.take_range, Nat.min_eq_left (show 8 ≤ ℓ by omega)]]
    simp [win, segF, List.range_eq_range', Function.comp_def]
  have tb := isBool hL hr0 (t_bool hL 1 (by omega))
  refine ⟨⟨by simp [akmOf]; omega, by simp [akmOf]⟩, ?_, ⟨k, by rw [← hwin]; exact hk,
    by rw [hn, winVal, hwin8], by rw [hfa]; exact cvOne.symm⟩, fun h => ?_, cv_bool tb, fun h j hj => ?_, ?_⟩
  · intro x hx
    simp only [akmOf, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx; exact bvA_lt hL (by omega)
  · obtain ⟨hl, hb⟩ := hfa1 (cvOne.mp h)
    refine ⟨by simp [akmOf, hl], ?_⟩
    simp [akmOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show 8 < ℓ by omega), hb]
  · have h0 : tr.cell tt s (t 1) = 0 := by
      rcases tb with t0 | t0
      · exact t0
      · exfalso; have h1 := cvOne.mpr t0; simp only [akmOf] at h; omega
    have hr : s + j < tr.height tt := by omega
    have e := con hL hr (mem_mem (e := mul3 (c sN) (not (c (t 1))) (sub (c pb) bE)) (by simp [cMem]))
    have ct := seg.const j (by omega) (t 1) (t_const hL 1 (by omega))
    simp only [eval_mul3, eval_not, eval_sub, eval_c, (hnon j hj).1, ct, h0, eval_bE hL hr] at e
    have hpb : tr.cell tt (s + j) pb = ((bvA tr tt (s + j) : Nat) : Fp) := by grind
    have := bvA_lt hL hr
    simp [akmOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
      List.getElem?_range (show j < ℓ by omega), cv, hpb, natCast_eq]
    exact Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P; omega)
  · refine ⟨cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, fun x hx => ?_⟩
    simp only [akmOf, List.mem_map, List.mem_range] at hx
    obtain ⟨j, -, rfl⟩ := hx; exact cv_lt _ _ _ _

end

end ZkFormal.NearV3.D1.AkmProof

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near AkmProof

/-- **The `akmV3` view.** -/
theorem akm_view : AkmViewStmt := by
  intro tr pub tt hL
  have hpos : 0 < tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _
  obtain ⟨segs, hc, hend, hall, hpad⟩ : ∃ segs : List (Nat × Nat), Consec 0 segs ∧
      segEnd 0 segs ≤ tr.height tt ∧
      (∀ p ∈ segs, IsSeg (isOne tr tt AkmV3.act) (isOne tr tt AkmV3.af) (isOne tr tt AkmV3.al) p.1 p.2) ∧
      (∀ r, segEnd 0 segs ≤ r → r < tr.height tt → isOne tr tt AkmV3.act r = false) := by
    by_cases h0 : tr.cell tt 0 AkmV3.act = 1
    · exact segments_of (segFacts hL h0) hpos
    · refine ⟨[], trivial, by simp [segEnd], by simp, fun r _ hr => ?_⟩
      have : ∀ r, r < tr.height tt → tr.cell tt r AkmV3.act = 0 := by
        intro r
        induction r with
        | zero => intro _; exact zero_of_not_one hL hpos bool_act (by simp [isOne, h0])
        | succ r ih => intro hr; exact pad hL hr (ih (by omega))
      simp [isOne, this r hr]
  have hH : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height tt := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  have hseg : ∀ p ∈ segs, SegAt tr tt p.1 p.2 := fun p hp => segInfo hL (hall p hp) (hH p hp)
  have hpadT : ∀ bb sd, ∀ q, segEnd 0 segs ≤ q → q < tr.height tt →
      rowTraffic AkmV3.interactions tr tt q pub bb sd = [] := fun bb sd q h1 h2 =>
    inactiveA hL h2 (zero_of_not_one hL h2 bool_act (hpad q h1 h2)) bb sd
  have hlen : ∀ p ∈ segs, (akmOf tr tt p.1 p.2).bytes.length = p.2 := fun p _ => by simp [akmOf]
  have hsegT : ∀ bb sd, ∀ p ∈ segs, (List.range' p.1 p.2).flatMap
      (fun q => rowTraffic AkmV3.interactions tr tt q pub bb sd) =
      (if sd then akmSends [akmOf tr tt p.1 p.2] bb else akmRecvs [akmOf tr tt p.1 p.2] bb).map Msg.toFp := by
    intro bb sd p hp
    have W := segWf hL (hseg p hp)
    rw [List.range'_eq_map_range, List.flatMap_map,
      flatMap_congr' (fun j hj => rowLaneA hL (hseg p hp) j (List.mem_range.1 hj) bb sd), ← List.map_flatMap]
    have hsum := rowMsgsA_sum _ W.len.1 (fun h => (W.fullAccess h).1) bb sd
    rw [hlen p hp] at hsum
    rw [hsum]
  refine ⟨segs.map fun p => akmOf tr tt p.1 p.2, ⟨fun e he => ?_, ?_⟩, fun bb m => ⟨?_, ?_⟩⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact segWf hL (hseg p hp)
  · rw [List.map_map]
    have hsum : (segs.map fun p => p.2).sum = segEnd 0 segs := by
      have := congrArg List.length (range'_segs segs 0 hc)
      simp only [List.length_range', Nat.sub_zero, List.length_flatMap] at this
      rw [this]
    have : (segs.map ((fun e => e.bytes.length) ∘ fun p => akmOf tr tt p.1 p.2)) = segs.map fun p => p.2 :=
      List.map_congr_left (fun p hp => hlen p hp)
    rw [this, hsum]
    have := height_le hL
    simp only [AkmV3.maxLog]; omega
  · have hs : ∀ es : List AkmE, akmSends es bb = es.flatMap fun e => akmSends [e] bb := by
      intro es; unfold akmSends; repeat' split
      all_goals simp
    simp only [akmTraffic, tableBusCount_eq]
    rw [flatMap_rows_segs _ segs _ hc hend (hpadT bb true), hs, List.map_flatMap, List.flatMap_map]
    rw [flatMap_congr' (fun p hp => hsegT bb true p hp)]
    rfl
  · have hs : ∀ es : List AkmE, akmRecvs es bb = es.flatMap fun e => akmRecvs [e] bb := by
      intro es; unfold akmRecvs; repeat' split
      all_goals simp
    simp only [akmTraffic, tableBusCount_eq]
    rw [flatMap_rows_segs _ segs _ hc hend (hpadT bb false), hs, List.map_flatMap, List.flatMap_map]
    rw [flatMap_congr' (fun p hp => hsegT bb false p hp)]
    rfl

end ZkFormal.NearV3.D1
