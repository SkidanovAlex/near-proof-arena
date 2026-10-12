import ZkFormal.NearV3.Assembly.TrieA7Node

/-!
# ZkFormal.NearV3.Assembly.TrieA7Val — record-level traffic of `valA7`'s appended interactions

The A7 extension of `valV3` receives `RPLV (vid)` on the first row of every replaced value
record and sends `SIZE (4, rb)` on the `SUM` row.  With the replaced records chosen by a
predicate `S` on record indices (`selV es S`, the row choice of `valA7Trace`):

* `val_rpl_recvs`: the `RPLV` receives are `[t]` for the records `t` with `S t` (record `t` has
  `vid = t`, `ValWf.first`/`ids`);
* `val_size_sends`: the only `SIZE` send is `[4, valA7Total es S]`,
  `valA7Total es S = Σ_t (2 − [S t]) · len_t` (empty values have `len = 0`);
* `val_rpl_sends`, `val_size_recvs`: none.
-/

namespace ZkFormal.NearV3.Assembly.TrieA7

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.Render
  ZkFormal.NearV3.UnfoldA7

section Val
open ValGen

/-- The row choice of replaced value records. -/
def selV (es : List ValE) (S : Nat → Bool) (q : Nat) : Bool :=
  decide (q < ValGen.R es) && S ((recs es).getD q default).1

/-- The A7 value total `Σ_t (2 − [S t]) · len_t`. -/
def valA7Total (es : List ValE) (S : Nat → Bool) : Nat :=
  ((List.range es.length).map fun t => (if S t then 1 else 2) * (ent es t).len).sum

theorem val_base_cell (es : List ValE) (q x : Nat) (hq : q < (valTraceAligned es).height T_VAL)
    (hx : x < ZkFormal.NearV3.ValV3.width) :
    (valTraceAligned es).cell T_VAL q x = Fp.ofNat (ValGen.cell es ((valTraceAligned es).height T_VAL) q x) :=
  rowsTrace_mkTab _ _ _ _ q x hq hx

theorem val_height (es : List ValE) (hok : ValOk es) : ValGen.R es + 1 ≤ (valTraceAligned es).height T_VAL :=
  (padded_log_fits (ValGen.R es + 1) hok.wf.rows).1

theorem val_R_lt (es : List ValE) (hok : ValOk es) : ValGen.R es < 2 ^ 22 := by
  have h := hok.wf.rows
  have : ValGen.R es = (es.map fun e => if e.vz then 1 else e.len).sum := rfl
  omega

theorem val_length_le (es : List ValE) (hok : ValOk es) : es.length ≤ ValGen.R es := by
  have : ValGen.R es = ((List.range es.length).map fun t => nOf (ent es t)).sum := by
    rw [← recs_length]; simp [recs, List.length_flatMap]
  rw [this]
  have := length_le_sum (List.range es.length) (fun t => nOf (ent es t))
    (fun t ht => nOf_pos hok (List.mem_range.1 ht))
  simpa using this

theorem ent_vid (es : List ValE) (hok : ValOk es) : ∀ t, t < es.length → (ent es t).vid = t
  | 0, h => by
    have := hok.wf.first h
    simp only [ent, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
    exact this
  | t + 1, h => by
    rw [ids' hok h, ent_vid es hok t (by omega)]
    have := val_length_le es hok
    have := val_R_lt es hok
    have : (2 : Nat) ^ 22 < P := by decide
    exact Nat.mod_eq_of_lt (by omega)

theorem val_cells (es : List ValE) (S : Nat → Bool) (q : Nat)
    (hq : q < (valTraceAligned es).height T_VAL) :
    let tr := valA7Trace es T_VAL (selV es S)
    let H := (valTraceAligned es).height T_VAL
    tr.cell T_VAL q ZkFormal.NearV3.ValV3.vf = Fp.ofNat (ValGen.cell es H q 1) ∧
    tr.cell T_VAL q ZkFormal.NearV3.ValV3.vid = Fp.ofNat (ValGen.cell es H q 3) ∧
    tr.cell T_VAL q ZkFormal.NearV3.ValV3.sumr = Fp.ofNat (ValGen.cell es H q 12) ∧
    tr.cell T_VAL q Val.rplv =
      (if selV es S q = true ∧ Fp.ofNat (ValGen.cell es H q 1) = 1 then 1 else 0) ∧
    tr.cell T_VAL q Val.rb = prefixF (valInc (valTraceAligned es) T_VAL (selV es S)) q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [valA7Trace]; rw [cell_withCols_lt (by decide)]; exact val_base_cell es q _ hq (by decide)
  · simp only [valA7Trace]; rw [cell_withCols_lt (by decide)]; exact val_base_cell es q _ hq (by decide)
  · simp only [valA7Trace]; rw [cell_withCols_lt (by decide)]; exact val_base_cell es q _ hq (by decide)
  · simp only [valA7Trace]; rw [cell_withCols_ge (by decide)]
    simp only [valCols, Val.rplv, ite_true, valRpl]
    rw [val_base_cell es q ZkFormal.NearV3.ValV3.vf hq (by decide)]; rfl
  · simp only [valA7Trace]; rw [cell_withCols_ge (by decide)]
    simp [valCols, Val.rplv, Val.rb]

theorem vcell1_le (es : List ValE) (H q : Nat) : ValGen.cell es H q 1 ≤ 1 := by
  simp only [ValGen.cell]
  split
  · simp_all
  · split
    · simp only [recCell]; split <;> omega
    · split <;> omega

theorem val_rpl_row (es : List ValE) (S : Nat → Bool) (pub : List Fp) (q : Nat)
    (hq : q < (valTraceAligned es).height T_VAL) :
    (rowTraffic UnfoldA7.Val.interactions (valA7Trace es T_VAL (selV es S)) T_VAL q pub B_RPLV false).map
        (List.map Fp.toNat) =
      if selV es S q = true ∧ ValGen.cell es ((valTraceAligned es).height T_VAL) q 1 = 1 then
        [[ValGen.cell es ((valTraceAligned es).height T_VAL) q 3 % P]] else [] := by
  obtain ⟨cF, cI, -, cR, -⟩ := val_cells es S q hq
  have hb := vcell1_le es ((valTraceAligned es).height T_VAL) q
  have o1 : Fp.ofNat 1 = (1 : Fp) := by decide
  have o0 : Fp.ofNat 0 = (0 : Fp) := by decide
  have z : ((0 : Fp) = 1) = False := by decide
  have m11 : Fp.mul 1 1 = 1 := by decide
  have m10 : (Fp.mul 1 0 = 1) = False := by decide
  have m01 : (Fp.mul 0 1 = 1) = False := by decide
  have m00 : (Fp.mul 0 0 = 1) = False := by decide
  rcases (show ValGen.cell es ((valTraceAligned es).height T_VAL) q 1 = 0 ∨
      ValGen.cell es ((valTraceAligned es).height T_VAL) q 1 = 1 by omega) with h | h <;>
  by_cases hs : selV es S q = true <;>
  simp [rowTraffic, UnfoldA7.Val.interactions, Dsl.recv, Dsl.send, B_RPLV, B_SIZE, Interaction.multNat,
    Interaction.multNat.go, Interaction.msgVal, cF, cI, cR, h, hs, o1, o0, z, m11, m10, m01, m00]

theorem vrec_flat (es : List ValE) (hok : ValOk es) (S : Nat → Bool) :
    (List.range (ValGen.R es)).flatMap (fun q =>
      if (S ((recs es).getD q default).1 = true ∧ ((recs es).getD q default).2 = 0) then
        [[((recs es).getD q default).1]] else []) =
      (List.range es.length).flatMap (fun t => if S t = true then [[t]] else []) := by
  rw [← recs_length,
    ← ZkFormal.Near.Render.flatMap_getD default (recs es)
      (fun r => if (S r.1 = true ∧ r.2 = 0) then [[r.1]] else [])]
  simp only [recs, List.flatMap_assoc, List.flatMap_map]
  apply ZkFormal.Near.Render.flatMap_congr'
  intro t ht
  obtain ⟨m, hm⟩ : ∃ m, nOf (ent es t) = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (nOf_pos hok (List.mem_range.1 ht))).symm⟩
  rw [hm, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  rw [ZkFormal.Near.Render.flatMap_nil' (fun p _ => by simp)]
  simp

/-- **`RPLV` receives of the honest `valA7` trace**: one `[t]` per record `t` with `S t`. -/
theorem val_rpl_recvs (es : List ValE) (hok : ValOk es) (S : Nat → Bool) (pub : List Fp) :
    (traceTraffic UnfoldA7.Val.interactions (valA7Trace es T_VAL (selV es S)) T_VAL pub).recvs B_RPLV =
      ((List.range es.length).filter S).map fun t => [t] := by
  have hH := val_height es hok
  have hL := val_length_le es hok
  have hR := val_R_lt es hok
  have hP : (2 : Nat) ^ 22 < P := by decide
  simp only [traceTraffic]
  rw [show (valA7Trace es T_VAL (selV es S)).height T_VAL = (valTraceAligned es).height T_VAL from rfl]
  rw [ZkFormal.Near.Render.flatMap_congr' (fun q hq => val_rpl_row es S pub q (List.mem_range.1 hq)),
    ZkFormal.Near.Render.range_split (show ValGen.R es ≤ (valTraceAligned es).height T_VAL by omega),
    List.flatMap_append,
    ZkFormal.Near.Render.flatMap_nil' (l := List.map _ _) (fun q hq => by
      obtain ⟨q', _, rfl⟩ := List.mem_map.1 hq
      have : selV es S (ValGen.R es + q') = false := by
        simp only [selV, Bool.and_eq_false_imp, decide_eq_true_eq]; intro h; omega
      simp [this]),
    List.append_nil, ← flatMap_filter_single, ← vrec_flat es hok]
  apply ZkFormal.Near.Render.flatMap_congr'
  intro q hq
  have hq' := List.mem_range.1 hq
  have hmem := recs_mem (recs_getD_mem hq')
  have h1 : ValGen.cell es ((valTraceAligned es).height T_VAL) q 1 =
      if ((recs es).getD q default).2 = 0 then 1 else 0 := by simp [ValGen.cell, hq', recCell]
  have h3 : ValGen.cell es ((valTraceAligned es).height T_VAL) q 3 = ((recs es).getD q default).1 := by
    simp only [ValGen.cell, hq', recCell]; simp; exact ent_vid es hok _ hmem.1
  rw [h1, h3, Nat.mod_eq_of_lt (by omega)]
  simp only [selV, decide_eq_true hq', Bool.true_and]
  by_cases hs : S ((recs es).getD q default).1 = true <;>
    by_cases hp : ((recs es).getD q default).2 = 0 <;> simp [hs, hp]

/-- The per-row increment of `rb` on a record row. -/
def incV (es : List ValE) (S : Nat → Bool) (tp : Nat × Nat) : Fp :=
  (if (ent es tp.1).vz then 0 else 2) - (if S tp.1 = true ∧ tp.2 = 0 then Fp.ofNat (ent es tp.1).len else 0)

theorem valInc_row (es : List ValE) (S : Nat → Bool) (q : Nat) (hq : q < ValGen.R es)
    (hH : q < (valTraceAligned es).height T_VAL) :
    valInc (valTraceAligned es) T_VAL (selV es S) q = incV es S ((recs es).getD q default) := by
  have e : ∀ x, x < ZkFormal.NearV3.ValV3.width → x ≠ 11 → (valTraceAligned es).cell T_VAL q x =
      Fp.ofNat (recCell es ((recs es).getD q default) x) := fun x hx h11 => by
    rw [val_base_cell es q x hH hx]; simp [ValGen.cell, h11, hq]
  have hs : selV es S q = S ((recs es).getD q default).1 := by simp [selV, hq]
  simp only [valInc, valRpl, incV, hs, e _ (show ZkFormal.NearV3.ValV3.gb < _ by decide) (by decide),
    e _ (show ZkFormal.NearV3.ValV3.vf < _ by decide) (by decide),
    e _ (show ZkFormal.NearV3.ValV3.len < _ by decide) (by decide)]
  rw [show ZkFormal.NearV3.ValV3.gb = 13 from rfl, show ZkFormal.NearV3.ValV3.vf = 1 from rfl,
    show ZkFormal.NearV3.ValV3.len = 4 from rfl]
  have o1 : Fp.ofNat 1 = (1 : Fp) := by decide
  have o0 : Fp.ofNat 0 = (0 : Fp) := by decide
  have z : ((0 : Fp) = 1) = False := by decide
  by_cases h1 : S ((recs es).getD q default).1 = true <;>
    by_cases h2 : ((recs es).getD q default).2 = 0 <;>
    by_cases h3 : (ent es ((recs es).getD q default).1).vz = true <;>
    simp [recCell, h1, h2, h3, o1, o0, z] <;> grind

theorem vrec_inc (es : List ValE) (hok : ValOk es) (S : Nat → Bool) (t : Nat) (ht : t < es.length) :
    (((List.range (nOf (ent es t))).map fun p => (t, p)).map (incV es S)).foldr (· + ·) 0 =
      Fp.ofNat ((if S t then 1 else 2) * (ent es t).len) := by
  have hsh := shapeAt hok ht
  obtain ⟨m, hm⟩ : ∃ m, nOf (ent es t) = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (nOf_pos hok ht)).symm⟩
  rw [hm]
  simp only [List.range_succ_eq_map, List.map_cons, List.map_map, List.foldr_cons]
  have o0 : Fp.ofNat 0 = (0 : Fp) := by decide
  have o1 : Fp.ofNat 1 = (1 : Fp) := by decide
  cases hv : (ent es t).vz
  · have hlen : (ent es t).len = m + 1 := by rw [← hm]; simp [nOf, hv]
    have hrest : (List.range m).map (incV es S ∘ (fun p => (t, p)) ∘ Nat.succ) =
        (List.range m).map fun _ => (2 : Fp) := by
      apply List.map_congr_left; intro p _; simp [incV, hv] <;> grind
    rw [hrest, foldr_const2]
    simp only [incV, hv, Bool.false_eq_true, ite_false, and_true, hlen]
    have a2 : Fp.ofNat (2 * m) = Fp.ofNat m + Fp.ofNat m := by
      rw [show 2 * m = m + m by omega]; exact ZkFormal.Near.Render.RcptP.ofNat_add_e m m
    have a1 := ZkFormal.Near.Render.RcptP.ofNat_add_e m 1
    cases S t
    · simp only [Bool.false_eq_true, ite_false]
      rw [show 2 * (m + 1) = m + m + 1 + 1 by omega, ZkFormal.Near.Render.RcptP.ofNat_add_e,
        ZkFormal.Near.Render.RcptP.ofNat_add_e, ZkFormal.Near.Render.RcptP.ofNat_add_e, a2, o1]
      grind
    · simp only [ite_true, Nat.one_mul]
      rw [a1, a2, o1]
      grind
  · have hm0 : m = 0 := by have : nOf (ent es t) = 1 := by simp [nOf, hv]
                           omega
    have hl := (hsh.1 hv).1
    subst hm0
    simp [incV, hv, hl, o0] <;> grind

theorem val_total_lt (es : List ValE) (hok : ValOk es) (S : Nat → Bool) : valA7Total es S < P := by
  have h1 : valA7Total es S ≤ 2 * ValGen.R es := by
    have hR : ValGen.R es = ((List.range es.length).map fun t => nOf (ent es t)).sum := by
      rw [← recs_length]; simp [recs, List.length_flatMap]
    rw [hR, valA7Total]
    have : ∀ l : List Nat, (∀ t ∈ l, t < es.length) →
        (l.map fun t => (if S t then 1 else 2) * (ent es t).len).sum ≤ 2 * (l.map fun t => nOf (ent es t)).sum := by
      intro l hl
      induction l with
      | nil => simp
      | cons x l ih =>
        simp only [List.map_cons, List.sum_cons]
        have ih' := ih (fun t ht => hl t (by simp [ht]))
        have hx : (if S x then 1 else 2) * (ent es x).len ≤ 2 * nOf (ent es x) := by
          have hsh := shapeAt hok (hl x (by simp))
          unfold nOf
          cases hv : (ent es x).vz
          · simp only [Bool.false_eq_true, ite_false]; cases S x <;> simp <;> omega
          · simp [(hsh.1 hv).1]
        omega
    exact this _ (fun t ht => List.mem_range.1 ht)
  have := val_R_lt es hok
  have : 2 * 2 ^ 22 < P := by decide
  omega

theorem val_rb (es : List ValE) (hok : ValOk es) (S : Nat → Bool) :
    prefixF (valInc (valTraceAligned es) T_VAL (selV es S)) (ValGen.R es) = Fp.ofNat (valA7Total es S) := by
  have hH := val_height es hok
  rw [prefixF_eq, List.map_congr_left (g := fun q => incV es S ((recs es).getD q default))
    (fun q hq => valInc_row es S q (List.mem_range.1 hq) (by have := List.mem_range.1 hq; omega)),
    ← recs_length, map_getD default (incV es S) (recs es)]
  simp only [recs, List.map_flatMap, foldr_flatMap_fp]
  rw [List.map_congr_left (g := fun t => Fp.ofNat ((if S t then 1 else 2) * (ent es t).len))
    (fun t ht => vrec_inc es hok S t (List.mem_range.1 ht))]
  rw [show (List.range es.length).map (fun t => Fp.ofNat ((if S t then 1 else 2) * (ent es t).len)) =
      ((List.range es.length).map fun t => (if S t then 1 else 2) * (ent es t).len).map Fp.ofNat by
    simp only [List.map_map]; rfl, foldr_ofNat]
  rfl

/-- **`SIZE` sends of the honest `valA7` trace**: exactly `[4, valA7Total es S]`. -/
theorem val_size_sends (es : List ValE) (hok : ValOk es) (S : Nat → Bool) (pub : List Fp) :
    (traceTraffic UnfoldA7.Val.interactions (valA7Trace es T_VAL (selV es S)) T_VAL pub).sends B_SIZE =
      [[4, valA7Total es S]] := by
  have hH := val_height es hok
  have hrow : ∀ q, q < (valTraceAligned es).height T_VAL →
      (rowTraffic UnfoldA7.Val.interactions (valA7Trace es T_VAL (selV es S)) T_VAL q pub B_SIZE true).map
        (List.map Fp.toNat) = if q = ValGen.R es then [[4, valA7Total es S]] else [] := by
    intro q hq
    obtain ⟨-, -, cS, -, cA⟩ := val_cells es S q hq
    have o1 : Fp.ofNat 1 = (1 : Fp) := by decide
    have o0 : Fp.ofNat 0 = (0 : Fp) := by decide
    have z : ((0 : Fp) = 1) = False := by decide
    have h4 : (4 : Fp).toNat = 4 := rfl
    by_cases hqR : q = ValGen.R es
    · subst hqR
      have : ValGen.cell es ((valTraceAligned es).height T_VAL) (ValGen.R es) 12 = 1 := by
        simp [ValGen.cell]
      simp [rowTraffic, UnfoldA7.Val.interactions, Dsl.recv, Dsl.send, B_RPLV, B_SIZE, Interaction.multNat,
        Interaction.multNat.go, Interaction.msgVal, cS, cA, this, o1, val_rb es hok S, Fp.toNat_ofNat,
        Nat.mod_eq_of_lt (val_total_lt es hok S)]
      exact h4
    · have : ValGen.cell es ((valTraceAligned es).height T_VAL) q 12 = 0 := by
        simp only [ValGen.cell]
        split
        · simp_all
        · split
          · simp [recCell]
          · simp_all
      simp [rowTraffic, UnfoldA7.Val.interactions, Dsl.recv, Dsl.send, B_RPLV, B_SIZE, Interaction.multNat,
        Interaction.multNat.go, cS, this, o0, z, hqR]
  simp only [traceTraffic]
  rw [show (valA7Trace es T_VAL (selV es S)).height T_VAL = (valTraceAligned es).height T_VAL from rfl,
    ZkFormal.Near.Render.flatMap_congr' (fun q hq => hrow q (List.mem_range.1 hq))]
  rw [ZkFormal.Near.Render.range_split (show ValGen.R es + 1 ≤ (valTraceAligned es).height T_VAL from hH),
    List.range_succ, List.flatMap_append, List.flatMap_append,
    ZkFormal.Near.Render.flatMap_nil' (l := List.range (ValGen.R es)) (fun q hq => by
      have := List.mem_range.1 hq; simp; omega),
    ZkFormal.Near.Render.flatMap_nil' (l := List.map _ _) (fun q hq => by
      obtain ⟨q', _, rfl⟩ := List.mem_map.1 hq; simp; omega)]
  simp

/-- No `RPLV` sends. -/
theorem val_rpl_sends (es : List ValE) (sel : Nat → Bool) (pub : List Fp) :
    (traceTraffic UnfoldA7.Val.interactions (valA7Trace es T_VAL sel) T_VAL pub).sends B_RPLV = [] := by
  simp only [traceTraffic]
  apply ZkFormal.Near.Render.flatMap_nil'
  intro q _
  simp [rowTraffic, UnfoldA7.Val.interactions, Dsl.recv, Dsl.send, B_RPLV, B_SIZE]

/-- No `SIZE` receives. -/
theorem val_size_recvs (es : List ValE) (sel : Nat → Bool) (pub : List Fp) :
    (traceTraffic UnfoldA7.Val.interactions (valA7Trace es T_VAL sel) T_VAL pub).recvs B_SIZE = [] := by
  simp only [traceTraffic]
  apply ZkFormal.Near.Render.flatMap_nil'
  intro q _
  simp [rowTraffic, UnfoldA7.Val.interactions, Dsl.recv, Dsl.send, B_RPLV, B_SIZE]

end Val

end ZkFormal.NearV3.Assembly.TrieA7
