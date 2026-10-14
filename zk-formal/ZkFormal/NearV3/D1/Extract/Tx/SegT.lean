import ZkFormal.NearV3.D1.Extract.Tx.OpWf

/-!
# `ZkFormal.NearV3.D1.Extract.Tx.SegT` — the traffic of one op (16 rows)
-/

namespace ZkFormal.NearV3.D1.TxProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.TxV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- The messages of lane `j` of op `e` (as naturals). -/
def rowMsgs (e : TxE) (j bb : Nat) (sd : Bool) : List Msg :=
  if sd then
    (if bb = B_MEM ∧ e.s1 = 1 then
      [[e.vidA, e.op + 1, j, (e.lane j).mo, (e.lane j).lk, (e.lane j).st]] else []) ++
    (if bb = B_AKMEM ∧ e.s2 = 1 ∧ j < 8 then [[e.vidK, e.op + 1, j, (e.lane j).nk, e.fa]] else [])
  else
    (if bb = B_TXP then [[(e.lane j).g, e.kind, e.strict, e.okP, e.tov, e.stage, e.cok, (e.lane j).xN,
        (e.lane j).xB, (e.lane j).xC]] else []) ++
    (if bb = B_SIG ∧ j = 0 then [[e.op, e.valid]] else []) ++
    (if bb = B_FINAL ∧ j = 0 ∧ e.fW = 1 then [[W_TX + 2 * e.op, 0, 1 - e.s1, e.vidA]] else []) ++
    (if bb = B_FINAL ∧ j = 0 ∧ e.fK = 1 then [[W_TX + 2 * e.op + 1, 0, 1 - e.s2, e.vidK]] else []) ++
    (if bb = B_MEM ∧ e.s1 = 1 then
      [[e.vidA, e.tpA, j, (e.lane j).amt, (e.lane j).lk, (e.lane j).st]] else []) ++
    (if bb = B_AKMEM ∧ e.s2 = 1 ∧ j < 8 then [[e.vidK, e.tpK, j, (e.lane j).kn, e.fa]] else [])

theorem range16 : List.range 16 = List.range 8 ++ List.range' 8 8 := by decide

theorem flatMap_first {α : Type} (L : List α) :
    ((List.range 16).flatMap fun j => if j = 0 then L else []) = L := by
  rw [show List.range 16 = 0 :: List.range' 1 15 by decide, List.flatMap_cons, if_pos rfl,
    flatMap_range'_nil _ 1 15 (fun j _ => by simp [show 1 + j ≠ 0 by omega]), List.append_nil]

theorem flatMap_lt8 {α : Type} (m : Nat → α) :
    ((List.range 16).flatMap fun j => if j < 8 then [m j] else []) = (List.range 8).map m := by
  rw [range16, List.flatMap_append, flatMap_range'_nil _ 8 8 (fun j _ => by simp),
    List.append_nil, map_eq_flatMap]
  exact flatMap_congr' (fun j hj => by simp [List.mem_range.1 hj])

/-- The op's traffic is the 16 lanes' messages. -/
theorem rowMsgs_sum (e : TxE) (bb : Nat) (sd : Bool) :
    (List.range 16).flatMap (fun j => rowMsgs e j bb sd) =
      (if sd then txSends [e] bb else txRecvs [e] bb) := by
  cases sd
  · by_cases h1 : bb = B_TXP
    · subst h1; simp [rowMsgs, txRecvs, B_TXP, B_SIG, B_FINAL, B_MEM, B_AKMEM, map_eq_flatMap]
    by_cases h2 : bb = B_SIG
    · subst h2
      rw [flatMap_congr' (G := fun j => if j = 0 then [[e.op, e.valid]] else [])
        (fun j _ => by by_cases h : j = 0 <;> simp [h, rowMsgs, B_TXP, B_SIG, B_FINAL, B_MEM, B_AKMEM]),
        flatMap_first]
      simp [txRecvs, B_TXP, B_SIG]
    by_cases h3 : bb = B_FINAL
    · subst h3
      rw [flatMap_congr' (G := fun j => if j = 0 then
          ((if e.fW = 1 then [[W_TX + 2 * e.op, 0, 1 - e.s1, e.vidA]] else []) ++
           (if e.fK = 1 then [[W_TX + 2 * e.op + 1, 0, 1 - e.s2, e.vidK]] else [])) else [])
        (fun j _ => by by_cases h : j = 0 <;> simp [h, rowMsgs, B_TXP, B_SIG, B_FINAL, B_MEM, B_AKMEM]),
        flatMap_first]
      simp [txRecvs, B_TXP, B_SIG, B_FINAL]
    by_cases h4 : bb = B_MEM
    · subst h4
      by_cases hs : e.s1 = 1
      · rw [flatMap_congr' (G := fun j => [[e.vidA, e.tpA, j, (e.lane j).amt, (e.lane j).lk, (e.lane j).st]])
          (fun j _ => by simp [hs, rowMsgs, B_TXP, B_SIG, B_FINAL, B_MEM, B_AKMEM])]
        simp [txRecvs, hs, B_TXP, B_SIG, B_FINAL, B_MEM, map_eq_flatMap]
      · rw [flatMap_congr' (G := fun _ => []) (fun j _ => by simp [hs, rowMsgs, B_TXP, B_SIG, B_FINAL,
          B_MEM, B_AKMEM]), flatMap_nil_fun]
        simp [txRecvs, hs, B_TXP, B_SIG, B_FINAL, B_MEM]
    by_cases h5 : bb = B_AKMEM
    · subst h5
      by_cases hs : e.s2 = 1
      · rw [flatMap_congr' (G := fun j => if j < 8 then [[e.vidK, e.tpK, j, (e.lane j).kn, e.fa]] else [])
          (fun j _ => by simp [hs, rowMsgs, B_TXP, B_SIG, B_FINAL, B_MEM, B_AKMEM]), flatMap_lt8]
        simp [txRecvs, hs, B_TXP, B_SIG, B_FINAL, B_MEM, B_AKMEM]
      · rw [flatMap_congr' (G := fun _ => []) (fun j _ => by simp [hs, rowMsgs, B_TXP, B_SIG, B_FINAL,
          B_MEM, B_AKMEM]), flatMap_nil_fun]
        simp [txRecvs, hs, B_TXP, B_SIG, B_FINAL, B_MEM, B_AKMEM]
    rw [flatMap_congr' (G := fun _ => []) (fun j _ => by simp [rowMsgs, h1, h2, h3, h4, h5]),
      flatMap_nil_fun]
    simp [txRecvs, h1, h2, h3, h4, h5]
  · by_cases h4 : bb = B_MEM
    · subst h4
      by_cases hs : e.s1 = 1
      · rw [flatMap_congr' (G := fun j => [[e.vidA, e.op + 1, j, (e.lane j).mo, (e.lane j).lk, (e.lane j).st]])
          (fun j _ => by simp [hs, rowMsgs, B_MEM, B_AKMEM])]
        simp [txSends, hs, B_MEM, map_eq_flatMap]
      · rw [flatMap_congr' (G := fun _ => []) (fun j _ => by simp [hs, rowMsgs, B_MEM, B_AKMEM]),
          flatMap_nil_fun]
        simp [txSends, hs, B_MEM]
    by_cases h5 : bb = B_AKMEM
    · subst h5
      by_cases hs : e.s2 = 1
      · rw [flatMap_congr' (G := fun j => if j < 8 then [[e.vidK, e.op + 1, j, (e.lane j).nk, e.fa]] else [])
          (fun j _ => by simp [hs, rowMsgs, B_MEM, B_AKMEM]), flatMap_lt8]
        simp [txSends, hs, B_MEM, B_AKMEM]
      · rw [flatMap_congr' (G := fun _ => []) (fun j _ => by simp [hs, rowMsgs, B_MEM, B_AKMEM]),
          flatMap_nil_fun]
        simp [txSends, hs, B_MEM, B_AKMEM]
    rw [flatMap_congr' (G := fun _ => []) (fun j _ => by simp [rowMsgs, h4, h5]), flatMap_nil_fun]
    simp [txSends, h4, h5]

section
variable (hL : TableLocal TxV3.table tr tt pub)
include hL

theorem fWK_row {s : Nat} (hop : OpAt tr tt s) (j : Nat) (hj : j < 16) :
    tr.cell tt (s + j) fW = (if j = 0 then tr.cell tt s fW else 0) ∧
    tr.cell tt (s + j) fK = (if j = 0 then tr.cell tt s fK else 0) := by
  have hH := hop.h
  have hr : s + j < tr.height tt := by omega
  have hlf := hop.lf j hj
  have f12 := con hL hr (fmem (e := sub (c fW) (.mul (c lf) (c gW))) (by simp [cFlags]))
  have f13 := con hL hr (fmem (e := sub (c fK) (.mul (c lf) (c gK))) (by simp [cFlags]))
  simp only [eval_mul, eval_sub, eval_c, hlf] at f12 f13
  by_cases h0 : j = 0
  · subst h0; simp
  · simp only [h0, ite_false] at f12 f13 ⊢; exact ⟨by grind, by grind⟩

/-- **One lane's traffic.** -/
theorem rowLane {s : Nat} (hop : OpAt tr tt s) (j : Nat) (hj : j < 16) (bb : Nat) (sd : Bool) :
    rowTraffic TxV3.interactions tr tt (s + j) pub bb sd = (rowMsgs (txOf tr tt s) j bb sd).map Msg.toFp := by
  have hH := hop.h
  have hr : s + j < tr.height tt := by omega
  have ha := hop.act j hj
  have hla := hop.lane j hj
  have hlf := hop.lf j hj
  obtain ⟨hfw, hfk⟩ := fWK_row hL hop j hj
  have hgA := (laneFlags hL hop j hj).2.1
  have hc := fun x (hx : x ∈ opConst) => hop.const j hj x hx
  have b1 := isBool hL (r := s) (by omega) (x := s1) (by simp [boolCols])
  have b2 := isBool hL (r := s) (by omega) (x := s2) (by simp [boolCols])
  rw [rowT, ha, hlf, hfw, hfk, hgA, hla, hc op (by simp [opConst]), hc kind (by simp [opConst]),
    hc strict (by simp [opConst]), hc okP (by simp [opConst]), hc tov (by simp [opConst]),
    hc stage (by simp [opConst]), hc cok (by simp [opConst]), hc valid (by simp [opConst]),
    hc s1 (by simp [opConst]), hc s2 (by simp [opConst]), hc fa (by simp [opConst]),
    hc vidA (by simp [opConst]), hc vidK (by simp [opConst]), hc tpA (by simp [opConst]),
    hc tpK (by simp [opConst])]
  have eW : Fp.ofNat (W_TX + 2 * cv tr tt s op) = ((W_TX : Nat) : Fp) + ((2 : Nat) : Fp) * tr.cell tt s op := by
    rw [← ofNat_add', ← ofNat_mul', ofNat_cv]; rfl
  have eK : Fp.ofNat (W_TX + 2 * cv tr tt s op + 1) =
      ((W_TX : Nat) : Fp) + (((2 : Nat) : Fp) * tr.cell tt s op + (((1 : Nat) : Fp) + 0)) := by
    rw [← ofNat_add', ← ofNat_add', ← ofNat_mul', ofNat_cv, ← natCast_eq, ← natCast_eq, ← natCast_eq]
    grind
  have e1 : Fp.ofNat (cv tr tt s op + 1) = tr.cell tt s op + ((1 : Nat) : Fp) := by
    rw [← ofNat_add', ofNat_cv]; rfl
  have n1 : Fp.ofNat (1 - cv tr tt s s1) = 1 - tr.cell tt s s1 := by
    rcases cv_b b1 with ⟨a, c⟩ | ⟨a, c⟩ <;> rw [a, c] <;> decide
  have n2 : Fp.ofNat (1 - cv tr tt s s2) = 1 - tr.cell tt s s2 := by
    rcases cv_b b2 with ⟨a, c⟩ | ⟨a, c⟩ <;> rw [a, c] <;> decide
  have ej : Fp.ofNat j = ((j : Nat) : Fp) := rfl
  have e0 : Fp.ofNat 0 = ((0 : Nat) : Fp) := rfl
  have im : ∀ {C D : Prop} [Decidable C] [Decidable D] (m : Msg) (v : List Fp), (C ↔ D) →
      (D → Msg.toFp m = v) → (if C then [v] else []) = (if D then [m] else []).map Msg.toFp := by
    intro C D _ _ m v hCD h
    by_cases hD : D
    · rw [if_pos (hCD.mpr hD), if_pos hD]; simp [h hD]
    · rw [if_neg (fun hC => hD (hCD.mp hC)), if_neg hD]; rfl
  have i01 : ((if j = 0 then (1 : Fp) else 0) = 1) ↔ j = 0 := by
    by_cases h : j = 0 <;> simp [h, fp_zero_ne_one]
  have iW : ∀ x, ((if j = 0 then tr.cell tt s x else 0) = 1) ↔ (j = 0 ∧ cv tr tt s x = 1) := by
    intro x; by_cases h : j = 0 <;> simp [h, fp_zero_ne_one, cv_one_iff]
  have i8 : ((if j < 8 then tr.cell tt s s2 else 0) = 1) ↔ (cv tr tt s s2 = 1 ∧ j < 8) := by
    by_cases h : j < 8 <;> simp [h, fp_zero_ne_one, cv_one_iff]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  unfold rowMsgs
  rw [lane_txOf s j hj]
  simp only [laneOf, txOf]
  have tl : ∀ x, Msg.toFp [x] = [Fp.ofNat x] := fun _ => rfl
  cases sd
  · simp only [Bool.false_eq_true, ite_false, and_false, false_and, List.append_nil, List.map_append,
      and_true, true_and]
    refine ap (ap (ap (ap (ap ?_ ?_) ?_) ?_) ?_) ?_
    · exact im _ _ Iff.rfl (fun _ => by simp [Msg.toFp, ofNat_cv])
    · refine im _ _ ?_ (fun _ => ?_)
      · rw [i01]
      · simp [Msg.toFp, ofNat_cv]
    · refine im _ _ ?_ (fun _ => ?_)
      · rw [iW]
      · simp only [Msg.toFp, List.map_cons, List.map_nil, eW, e0, n1, ofNat_cv]
    · refine im _ _ ?_ (fun _ => ?_)
      · rw [iW]
      · simp only [Msg.toFp, List.map_cons, List.map_nil, eK, e0, n2, ofNat_cv]
    · refine im _ _ ?_ (fun _ => ?_)
      · rw [cv_one_iff]
      · simp only [Msg.toFp, List.map_cons, List.map_nil, ej, ofNat_cv]
    · refine im _ _ ?_ (fun _ => ?_)
      · rw [i8]
      · simp only [Msg.toFp, List.map_cons, List.map_nil, ej, ofNat_cv]
  · simp only [ite_true, and_false, false_and, ite_false, List.nil_append, List.append_nil,
      List.map_append, and_true, true_and, Bool.true_eq_false]
    refine ap ?_ ?_
    · refine im _ _ ?_ (fun _ => ?_)
      · rw [cv_one_iff]
      · simp only [Msg.toFp, List.map_cons, List.map_nil, ej, e1, ofNat_cv]
    · refine im _ _ ?_ (fun _ => ?_)
      · rw [i8]
      · simp only [Msg.toFp, List.map_cons, List.map_nil, ej, e1, ofNat_cv]

end

end ZkFormal.NearV3.D1.TxProof
