import ZkFormal.NearV3.Render.UnfoldA7Ext
import ZkFormal.NearV3.Render.PaddedTrie
import ZkFormal.NearV3.Render.PaddedUps
import ZkFormal.NearV3.Render.PaddedRcpt

/-!
# ZkFormal.NearV3.Render.UnfoldA7Aligned — aligned renders of the four A7 tables

For `nodeA7`, `valA7`, `upsA7`, `sizeA7` (indices 2, 4, 7, 21 of `nearAirV3`): the base
aligned render (`node_aligned_complete`, `val_aligned_complete`, `ups_aligned_complete`,
`size_aligned_complete`) with the honest A7 columns filled (`Render/UnfoldA7Ext.lean`) is
locally legal, roll-aligned, and has the **exact traffic** `base ⊕ traceTraffic`, where
`traceTraffic js` lists, row by row, the messages the appended interactions `js` emit
(`traceTraffic_exact`; the base traffic is unchanged, `tableBusCount_withCols`).  These are
the `TableRenderV3` components of the four tables.
-/

namespace ZkFormal.NearV3.UnfoldA7

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.Render

/-- The messages interactions `js` emit on the rows of table `t` (as naturals). -/
def traceTraffic (js : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp) : Traffic :=
  ⟨fun b => (List.range (tr.height t)).flatMap fun r =>
      (rowTraffic js tr t r pub b true).map (List.map Fp.toNat),
   fun b => (List.range (tr.height t)).flatMap fun r =>
      (rowTraffic js tr t r pub b false).map (List.map Fp.toNat)⟩

theorem toFp_toNat (l : List Fp) : Msg.toFp (l.map Fp.toNat) = l := by
  simp [Msg.toFp, List.map_map, Function.comp_def, Fp.ofNat_toNat]

theorem traceTraffic_map (js : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (b : Nat) (s : Bool) :
    ((if s then (traceTraffic js tr t pub).sends b else (traceTraffic js tr t pub).recvs b).map
      Msg.toFp) = (List.range (tr.height t)).flatMap fun r => rowTraffic js tr t r pub b s := by
  cases s <;>
  · simp only [traceTraffic, Bool.false_eq_true, ite_false, ite_true, List.map_flatMap, List.map_map]
    congr 1; funext r
    rw [show (Msg.toFp ∘ List.map Fp.toNat) = id from funext toFp_toNat, List.map_id]

/-- **Exact traffic of any interaction list**, read off the trace. -/
theorem traceTraffic_exact (js : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp) :
    TableTraffic js tr t pub (traceTraffic js tr t pub) := by
  intro b m
  refine ⟨?_, ?_⟩
  · rw [tableBusCount_eq]
    have := traceTraffic_map js tr t pub b true
    simp only [ite_true] at this
    rw [this]
  · rw [tableBusCount_eq]
    have := traceTraffic_map js tr t pub b false
    simp only [Bool.false_eq_true, ite_false] at this
    rw [this]

theorem tableBusCount_app (is js : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (b : Nat) (s : Bool) (m : List Fp) :
    tableBusCount (is ++ js) tr t pub b s m =
      tableBusCount is tr t pub b s m + tableBusCount js tr t pub b s m := by
  simp only [tableBusCount_eq, rowTraffic, List.flatMap_append]
  generalize List.range (tr.height t) = rs
  induction rs with
  | nil => simp
  | cons r rs ih => simp only [List.flatMap_cons, List.count_append, ih]; omega

/-- Concatenated traffic. -/
def Traffic.append (a b : Traffic) : Traffic :=
  ⟨fun x => a.sends x ++ b.sends x, fun x => a.recvs x ++ b.recvs x⟩

theorem tableTraffic_append {is js : List Interaction} {tr : Trace Fp} {t : Nat} {pub : List Fp}
    {ta tb : Traffic} (ha : TableTraffic is tr t pub ta) (hb : TableTraffic js tr t pub tb) :
    TableTraffic (is ++ js) tr t pub (Traffic.append ta tb) := by
  intro b m
  have e := tableBusCount_app is js tr t pub b
  refine ⟨?_, ?_⟩
  · rw [e, (ha b m).1, (hb b m).1]
    simp [Traffic.append, List.map_append, List.count_append]
  · rw [e, (ha b m).2, (hb b m).2]
    simp [Traffic.append, List.map_append, List.count_append]

/-- Base traffic survives filling columns `≥ w`. -/
theorem tableTraffic_withCols {is : List Interaction} {tr : Trace Fp} {t w : Nat} {pub : List Fp}
    {f : Nat → Nat → Fp} {tf : Traffic} (hw : ∀ i ∈ is, ∀ e ∈ i.mult ++ i.msg, e.colBound ≤ w)
    (h : TableTraffic is tr t pub tf) : TableTraffic is (Trace.withCols tr t w f) t pub tf := by
  intro b m
  rw [tableBusCount_withCols tr t w f pub is hw, tableBusCount_withCols tr t w f pub is hw]
  exact h b m

/-- Interaction expressions of a table are among its expressions. -/
theorem interaction_exprs_of {T : ZkFormal.Air.Table} {w : Nat} (h : ∀ e ∈ T.exprs, e.colBound ≤ w) :
    ∀ i ∈ T.interactions, ∀ e ∈ i.mult ++ i.msg, e.colBound ≤ w :=
  fun i hi e he => h e (List.mem_append_right _ (List.mem_flatMap.2 ⟨i, hi, he⟩))

/-! ## The four aligned renders -/

/-- The honest `nodeA7` trace (replaced records chosen by `sel` on first rows). -/
def nodeA7Trace (vs : List NodeS3) (t : Nat) (sel : Nat → Bool) : Trace Fp :=
  Trace.withCols (nodeTraceAligned vs) t 186 (nodeCols (nodeTraceAligned vs) t sel)

theorem nodeA7_aligned_complete (vs : List NodeS3) (hok : NodeOk vs) (t : Nat) (pub : List Fp)
    (sel : Nat → Bool) :
    TableLocal nodeA7 (nodeA7Trace vs t sel) t pub ∧
    TableTraffic nodeA7.interactions (nodeA7Trace vs t sel) t pub
      (Traffic.append (nodeTraffic3 vs) (traceTraffic Node.interactions (nodeA7Trace vs t sel) t pub)) ∧
    (nodeA7Trace vs t sel).log t % 3 = 1 := by
  obtain ⟨hL, hT, hA⟩ := node_aligned_complete vs hok t pub
  exact ⟨nodeA7_local sel hL,
    tableTraffic_append (tableTraffic_withCols (interaction_exprs_of node_colBound) hT)
      (traceTraffic_exact _ _ _ _), hA⟩

/-- The honest `valA7` trace. -/
def valA7Trace (es : List ValE) (t : Nat) (sel : Nat → Bool) : Trace Fp :=
  Trace.withCols (valTraceAligned es) t 15 (valCols (valTraceAligned es) t sel)

theorem valA7_aligned_complete (es : List ValE) (hok : ValOk es) (t : Nat) (pub : List Fp)
    (sel : Nat → Bool) :
    TableLocal valA7 (valA7Trace es t sel) t pub ∧
    TableTraffic valA7.interactions (valA7Trace es t sel) t pub
      (Traffic.append (valTraffic es) (traceTraffic Val.interactions (valA7Trace es t sel) t pub)) ∧
    (valA7Trace es t sel).log t % 3 = 1 := by
  obtain ⟨hL, hT, hA⟩ := val_aligned_complete es hok t pub
  exact ⟨valA7_local sel hL,
    tableTraffic_append (tableTraffic_withCols (interaction_exprs_of val_colBound) hT)
      (traceTraffic_exact _ _ _ _), hA⟩

/-- The honest `upsA7` trace. -/
def upsA7Trace (insts : List UpsInst) (t : Nat) : Trace Fp :=
  Trace.withCols (upsTraceAligned insts) t 200 (upsCols (upsTraceAligned insts) t)

theorem upsA7_aligned_complete (insts : List UpsInst) (h : UpsRenderOk insts) (t : Nat)
    (pub : List Fp) :
    TableLocal upsA7 (upsA7Trace insts t) t pub ∧
    TableTraffic upsA7.interactions (upsA7Trace insts t) t pub
      (Traffic.append (upsTraffic (UpsRows.viewOf (upsTraceAligned insts) t (UpsGen.segsOf insts)))
        (traceTraffic Ups.interactions (upsA7Trace insts t) t pub)) ∧
    (upsA7Trace insts t).log t % 3 = 1 := by
  obtain ⟨hL, hT, hA⟩ := ups_aligned_complete insts h t pub
  exact ⟨upsA7_local hL,
    tableTraffic_append (tableTraffic_withCols (interaction_exprs_of ups_colBound) hT)
      (traceTraffic_exact _ _ _ _), hA⟩

/-- The honest `sizeA7` trace, with the received A7 totals `yN` on rows `0, 1, 2`. -/
def sizeA7Trace (pub : List Fp) (v : SizeV) (t : Nat) (yN : Nat → Nat) : Trace Fp :=
  Trace.withCols (sizeTraceAligned pub v) t 31 (sizeCols yN)

theorem sizeA7_aligned_complete (pub : List Fp) (v : SizeV) (ok : SizeOk pub v) (t : Nat)
    (yN : Nat → Nat)
    (hB : ∀ r, r < (sizeTraceAligned pub v).height t →
      (sizeTraceAligned pub v).cell t r ZkFormal.NearV3.SizeV3.la = 1 → sizeU yN r ≤ B0) :
    TableLocal sizeA7 (sizeA7Trace pub v t yN) t pub ∧
    TableTraffic sizeA7.interactions (sizeA7Trace pub v t yN) t pub
      (Traffic.append (sizeTraffic v) (traceTraffic Size.interactions (sizeA7Trace pub v t yN) t pub)) ∧
    (sizeA7Trace pub v t yN).log t % 3 = 1 := by
  obtain ⟨hL, hT, hA⟩ := size_aligned_complete pub v ok t
  exact ⟨sizeA7_local yN hL hB,
    tableTraffic_append (tableTraffic_withCols (interaction_exprs_of size_colBound) hT)
      (traceTraffic_exact _ _ _ _), hA⟩

end ZkFormal.NearV3.UnfoldA7
