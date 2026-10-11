import ZkFormal.NearV3.Render.Padded
import ZkFormal.NearV3.Render.UpsRender
import ZkFormal.NearV3.Render.Ups.Local
import ZkFormal.NearV3.Render.Ups.GPlan
import ZkFormal.NearV3.Render.Ups.GFieldsComplete
import ZkFormal.NearV3.Render.Ups.GBytes
import ZkFormal.NearV3.Render.Ups.GMem

/-!
# Aligned `upsV3` generator (`nearAirV3` table 7, cap 22)

`upsTraceAligned insts` is the array-backed honest `upsV3` table (`UpsGen.cell`, M7d) at
`padLog22 (logOf (R + 1))`.  `ups_aligned_complete` assembles **all ten constraint groups**
(`cBool cRows cConst cWalk cSeg cPlan cFields cBytes cDigest cMem`) into `TableLocal UpsV3.table`
and gives the traffic of the soundness view `upsTraffic (viewOf tr t (segsOf insts))`
(`ups_view`/`ups_render_traffic`), at any height `2^L ≥ R + 1` (`ups_render_local_at`,
`ups_render_traffic_at` generalise `Ups/Local`, `Ups/Traffic` from the natural height).

**Honest-input condition** (`UpsRenderOk`): `UpsOk` (instances and the row cap) plus, for every
part `k < nQ I` of every instance, the per-part inputs the group lemmas take: `PartOk` (plan),
`FieldsOk` and `WindowOk` (field grammar, window roles), `ByteInput` (byte provenance;
`NodeEncoding` data, required inhabited) and `MemOk` (memory carries).  These are the explicit
M7d inputs; deriving them from native execution (`Ups/Native*`) is the open part of M7d.
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.NearV3.UpsRows
open ZkFormal.Size

open UpsGen in
/-- `ups_render_local_of` at any height `2^log`, `1 ≤ log ≤ 22`, holding the rows. -/
theorem ups_render_local_at (insts : List UpsInst) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : 1 ≤ tr.log t ∧ tr.log t ≤ 22)
    (hcell : ∀ r x, r < tr.height t → x < 200 → tr.cell t r x = ((cell insts r x : Int) : Fp))
    (hG : GroupOk insts (tr.height t) UpsV3.constraints) :
    TableLocal UpsV3.table tr t pub := by
  have hcon := constr_of (pub := pub) hcell hG
  refine ⟨hlog.1, hlog.2, hcon, ?_⟩
  intro r hr i hi g hg
  have ok : URowOk (rowC tr t r) (rowC tr t ((r + 1) % tr.height t)) := by
    intro e he hp
    rw [← eval_pure tr t r pub e hp]
    exact hcon r hr e he
  have hp : g.pure = true := by
    have h := List.all_eq_true.1 interactions_pure i hi
    simp only [Bool.and_eq_true] at h
    have h1 := h.1
    unfold pureGate at h1
    split at h1
    · rename_i g' hgm
      rw [hgm] at hg; simp only [List.mem_singleton] at hg; subst hg; exact h1
    · exact absurd h1 (by simp)
  rw [eval_pure tr t r pub g hp]
  exact gates01 ok (fun x => rowC_lt tr t r x) (fun x => rowC_lt tr t _ x) i hi g hg

open UpsGen in
/-- `ups_render_traffic` at any height holding the rows and one padding row. -/
theorem ups_render_traffic_at (insts : List UpsInst) (hs : UpsShape insts) (tr : Trace Fp) (t : Nat)
    (pub : List Fp) (hL : TableLocal UpsV3.table tr t pub) (hH : R insts + 1 ≤ tr.height t)
    (hcell : ∀ r x, r < tr.height t → x < 200 → tr.cell t r x = ((cell insts r x : Int) : Fp)) :
    TableTraffic UpsV3.interactions tr t pub (upsTraffic (UpsRows.viewOf tr t (segsOf insts))) := by
  refine UpsRows.viewTraffic hL consec_segs (by rw [segEnd_R]; omega) (segs_isSeg hs hH hcell) ?_
  intro r h1 h2
  rw [segEnd_R] at h1
  simp only [UpsRows.actB, decide_eq_false_iff_not]
  rw [rowC_cell hcell h2 (by decide), cell_pad (by omega)]
  decide

open UpsGen in
/-- **The honest-input condition of the `upsV3` render** (see the module doc). -/
structure UpsRenderOk (insts : List UpsInst) : Prop where
  ok : UpsOk insts
  parts : ∀ I ∈ insts, ∀ k, k < nQ I → PartOk I k (part I k)
  fields : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k)
  windows : ∀ I ∈ insts, ∀ k, k < nQ I → WindowOk I (part I k)
  bytes : ∀ I ∈ insts, ∀ k, k < nQ I → Nonempty (ByteInput I (part I k))
  mem : ∀ I ∈ insts, ∀ k, k < nQ I → MemOk I (part I k)

open UpsGen in
/-- All constraints of `upsV3` vanish on the honest rows at any height `H ≥ R + 1`. -/
theorem ups_groupOk (insts : List UpsInst) (h : UpsRenderOk insts) {H : Nat} (hH : R insts + 1 ≤ H) :
    GroupOk insts H UpsV3.constraints := by
  have ok := h.ok
  have hb : ∀ I ∈ insts, ∀ k, k < nQ I → ByteInput I (part I k) :=
    fun I hI k hk => Classical.choice (h.bytes I hI k hk)
  unfold UpsV3.constraints
  exact groupOk_append (groupOk_append (groupOk_append (groupOk_append (groupOk_append
    (groupOk_append (groupOk_append (groupOk_append (groupOk_append
    (cBool_ok ok hH) (cRows_ok ok hH)) (cConst_ok ok hH)) (cWalk_ok ok hH)) (cSeg_ok ok hH))
    (cPlan_ok ok h.parts hH)) (cFields_ok ok h.fields h.windows hH)) (cBytes_ok ok hb hH))
    (cDigest_ok ok hH)) (cMem_ok ok h.fields h.mem hH)

/-- The aligned, array-backed `upsV3` table (cells: canonical naturals of the integer cells). -/
def upsTraceAligned (insts : List UpsInst) : Trace Fp :=
  let log := padLog22 (logOf (UpsGen.R insts + 1))
  rowsTrace log (mkTab (2 ^ log) 200 (fun r c => ((UpsGen.cell insts r c : Int) : Fp).toNat))

open UpsGen in
/-- **`upsV3` aligned completeness** under the explicit honest-input condition `UpsRenderOk`. -/
theorem ups_aligned_complete (insts : List UpsInst) (h : UpsRenderOk insts) (t : Nat) (pub : List Fp) :
    TableLocal UpsV3.table (upsTraceAligned insts) t pub ∧
    TableTraffic UpsV3.interactions (upsTraceAligned insts) t pub
      (upsTraffic (UpsRows.viewOf (upsTraceAligned insts) t (segsOf insts))) ∧
    (upsTraceAligned insts).log t % 3 = 1 := by
  have hh := padded_log_fits (R insts + 1) h.ok.cap
  have hlog : (upsTraceAligned insts).log t = padLog22 (logOf (R insts + 1)) := rfl
  have hH : R insts + 1 ≤ (upsTraceAligned insts).height t := by
    unfold Trace.height; rw [hlog]; exact hh.1
  have hcell : ∀ r x, r < (upsTraceAligned insts).height t → x < 200 →
      (upsTraceAligned insts).cell t r x = ((cell insts r x : Int) : Fp) := by
    intro r x hr hx
    unfold Trace.height at hr; rw [hlog] at hr
    unfold upsTraceAligned
    rw [rowsTrace_mkTab _ _ _ t r x hr hx, Fp.ofNat_toNat]
  have hL := ups_render_local_at insts _ t pub (by rw [hlog]; exact ⟨hh.2.1, hh.2.2.1⟩) hcell
    (ups_groupOk insts h hH)
  exact ⟨hL, ups_render_traffic_at insts h.ok.shape _ t pub hL hH hcell, by rw [hlog]; exact hh.2.2.2⟩

end ZkFormal.NearV3.Render
