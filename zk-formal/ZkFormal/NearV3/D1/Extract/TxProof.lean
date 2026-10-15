import ZkFormal.NearV3.D1.Extract.Tx.SegT

/-!
# `ZkFormal.NearV3.D1.Extract.TxProof` — **the `txV3` view** (`tx_view : TxViewStmt`)

Lane `v3-d1-phase2` (milestone V2).  Statement: `Extract/TxView.lean`.  The rows split into
16-row ops (`Tx.Rows.segInfo`); each op's entry is `txOf` with the facts `opWf` (flags, gates,
written values, memory times; under byte inputs the chain results `Tx.Chain*` and the verdict
`Tx.Verdict` give `TxE.Arith`); its traffic is `rowMsgs` lane by lane (`Tx.SegT`).
-/

namespace ZkFormal.NearV3.D1.TxProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.TxV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

section
variable (hL : TableLocal TxV3.table tr tt pub)
include hL

/-- An inactive row carries no traffic. -/
theorem inactive {r : Nat} (hr : r < tr.height tt) (ha : tr.cell tt r act = 0) (bb : Nat) (sd : Bool) :
    rowTraffic TxV3.interactions tr tt r pub bb sd = [] := by
  have hlf := ((rowFacts hL hr).2.2.2 ha).1
  have f3 := con hL hr (fmem (e := .mul (c s1) (not (c act))) (by simp [cFlags]))
  have f2 := con hL hr (fmem (e := .mul (c s2) (not (c s1))) (by simp [cFlags]))
  have f11 := con hL hr (fmem (e := sub (c gA) (.mul (c s2) lo8)) (by simp [cFlags]))
  have f12 := con hL hr (fmem (e := sub (c fW) (.mul (c lf) (c gW))) (by simp [cFlags]))
  have f13 := con hL hr (fmem (e := sub (c fK) (.mul (c lf) (c gK))) (by simp [cFlags]))
  simp only [eval_mul, eval_sub, eval_c, eval_not, ha, hlf] at f3 f2 f11 f12 f13
  have h1 : tr.cell tt r s1 = 0 := by grind
  rw [h1] at f2
  have h2 : tr.cell tt r s2 = 0 := by grind
  rw [h2] at f11
  rw [rowT, ha, hlf, h1, show tr.cell tt r gA = 0 by grind, show tr.cell tt r fW = 0 by grind,
    show tr.cell tt r fK = 0 by grind]
  simp [fp_zero_ne_one]

end

end ZkFormal.NearV3.D1.TxProof

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near TxProof

/-- **The `txV3` view.** -/
theorem tx_view : TxViewStmt := by
  intro tr pub tt hL
  have hpos : 0 < tr.height tt := by unfold Trace.height; exact Nat.two_pow_pos _
  obtain ⟨segs, hc, hend, hall, hpad⟩ : ∃ segs : List (Nat × Nat), Consec 0 segs ∧
      segEnd 0 segs ≤ tr.height tt ∧
      (∀ p ∈ segs, IsSeg (isOne tr tt TxV3.act) (isOne tr tt TxV3.lf) (isOne tr tt TxV3.ll) p.1 p.2) ∧
      (∀ r, segEnd 0 segs ≤ r → r < tr.height tt → isOne tr tt TxV3.act r = false) := by
    by_cases h0 : tr.cell tt 0 TxV3.act = 1
    · exact segments_of (segFacts hL h0) hpos
    · refine ⟨[], trivial, by simp [segEnd], by simp, fun r _ hr => ?_⟩
      have : ∀ r, r < tr.height tt → tr.cell tt r TxV3.act = 0 := by
        intro r
        induction r with
        | zero => intro _; exact zero_of_not_one hL hpos bool_act (by simp [isOne, h0])
        | succ r ih => intro hr; exact pad hL hr (ih (by omega))
      simp [isOne, this r hr]
  have hH : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height tt := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  have hop : ∀ p ∈ segs, p.2 = 16 ∧ OpAt tr tt p.1 := fun p hp => opAt_of hL (hall p hp) (hH p hp)
  have hpadT : ∀ bb sd, ∀ q, segEnd 0 segs ≤ q → q < tr.height tt →
      rowTraffic TxV3.interactions tr tt q pub bb sd = [] := fun bb sd q h1 h2 =>
    inactive hL h2 (zero_of_not_one hL h2 bool_act (hpad q h1 h2)) bb sd
  have hseg : ∀ bb sd, ∀ p ∈ segs, (List.range' p.1 p.2).flatMap
      (fun q => rowTraffic TxV3.interactions tr tt q pub bb sd) =
      (if sd then txSends [txOf tr tt p.1] bb else txRecvs [txOf tr tt p.1] bb).map Msg.toFp := by
    intro bb sd p hp
    obtain ⟨h16, ho⟩ := hop p hp
    rw [h16, List.range'_eq_map_range, List.flatMap_map,
      flatMap_congr' (fun j hj => rowLane hL ho j (List.mem_range.1 hj) bb sd), ← List.map_flatMap,
      rowMsgs_sum]
  refine ⟨segs.map fun p => txOf tr tt p.1, ⟨fun e he => ?_, ?_⟩, fun bb m => ⟨?_, ?_⟩⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact opWf hL (hop p hp).2
  · rw [List.length_map]
    have hsum : (segs.map fun p => p.2).sum = segEnd 0 segs := by
      have := congrArg List.length (range'_segs segs 0 hc)
      simp only [List.length_range', Nat.sub_zero, List.length_flatMap] at this
      rw [this]
    have : (segs.map fun p => p.2) = segs.map fun _ => 16 := List.map_congr_left (fun p hp => (hop p hp).1)
    rw [this] at hsum
    have e : ∀ l : List (Nat × Nat), (l.map fun _ => 16).sum = 16 * l.length := by
      intro l; induction l with
      | nil => rfl
      | cons _ l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega
    rw [e] at hsum
    have := height_le hL
    simp only [TxV3.maxLog]; omega
  · have hs : ∀ es : List TxE, txSends es bb = es.flatMap fun e => txSends [e] bb := by
      intro es; unfold txSends; repeat' split
      all_goals simp
    simp only [txTraffic, tableBusCount_eq]
    rw [flatMap_rows_segs _ segs _ hc hend (hpadT bb true), hs, List.map_flatMap, List.flatMap_map]
    rw [flatMap_congr' (fun p hp => hseg bb true p hp)]
    rfl
  · have hs : ∀ es : List TxE, txRecvs es bb = es.flatMap fun e => txRecvs [e] bb := by
      intro es; unfold txRecvs; repeat' split
      all_goals simp [map_eq_flatMap]
    simp only [txTraffic, tableBusCount_eq]
    rw [flatMap_rows_segs _ segs _ hc hend (hpadT bb false), hs, List.map_flatMap, List.flatMap_map]
    rw [flatMap_congr' (fun p hp => hseg bb false p hp)]
    rfl

end ZkFormal.NearV3.D1
