import ZkFormal.NearV3.Render.Padded
import ZkFormal.NearV3.Rcpt.Render.Srcp.LocalProof
import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficProof
import ZkFormal.NearV3.Rcpt.Render.Srcp.ProofComplete

/-!
# Concrete aligned generator for the source-proof table `srcpV3`

As `Render/Padded.lean`: the honest rows `SrcpGen.cell bs` (root row, 32 leaf rows and
64 rows per path item per used source proof; padding carries the final `SIZE`
accumulator) in an array-backed trace of height `2^padLog22 (logOf R)`.  The hypothesis
is exactly the view's `SrcpWf bs` (`Rcpt/Extract/Srcp/Proof.lean:srcp_view`), whose row
bound `srcpRows bs ≤ 2^22` is what A10 (`Rcpt/SrcpDepth.lean`) provides for an honest
witness.  `srcpV3` already has `maxLog = 22`, so no cap changes.
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Size

namespace SrcpGen

/-- Columns beyond the table width are zero in every generated row. -/
theorem cell_high (bs : List SrcpB) (r x : Nat) (hx : SrcpV3.width ≤ x) : cell bs r x = 0 := by
  have hx' : x = (x - 22) + 22 := by unfold SrcpV3.width at hx; omega
  unfold cell
  split
  · rw [hx']
    simp only [Frame.cell]
    unfold SrcpV3.width at hx
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [if_neg (by unfold SrcpV3.sz; unfold SrcpV3.width at hx; omega)]

/-- **Honest source-table local legality at any height `≥ R bs` within a cap.** -/
theorem table_local_at {bs : List SrcpB} (h : SrcpWf bs) {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hlog : 1 ≤ tr.log tt ∧ tr.log tt ≤ SrcpV3.maxLog) (hH : R bs ≤ tr.height tt)
    (hc : ∀ r, r < tr.height tt → ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x)) :
    TableLocal SrcpV3.table tr tt pub := by
  refine ⟨hlog.1, hlog.2, ?_, ?_⟩
  · intro r hr ex hex
    have hn : (r + 1) % tr.height tt < tr.height tt := Nat.mod_lt _ (by omega)
    exact constraints h hH hr (hc r hr) (hc _ hn) ex hex
  · intro r hr
    exact mult_bits (hc r hr)

end SrcpGen

def srcpTraceAligned (bs : List SrcpB) : Trace Fp :=
  let log := padLog22 (logOf (SrcpGen.R bs))
  rowsTrace log (mkTab (2 ^ log) SrcpV3.width (SrcpGen.cell bs))

/-- **Source-proof table completeness at the aligned height** (within its cap `22`), with
exactly the view's traffic `srcpTraffic bs`. -/
theorem srcp_aligned_complete (bs : List SrcpB) (h : SrcpWf bs) (t : Nat) (pub : List Fp) :
    TableLocal SrcpV3.table (srcpTraceAligned bs) t pub ∧
    TableTraffic SrcpV3.interactions (srcpTraceAligned bs) t pub (srcpTraffic bs) ∧
    (srcpTraceAligned bs).log t % 3 = 1 := by
  have hR : SrcpGen.R bs ≤ 2 ^ 22 := by rw [SrcpGen.R_eq]; exact h.rows
  have hh := padded_log_fits (SrcpGen.R bs) hR
  have hc : ∀ r, r < (srcpTraceAligned bs).height t → ∀ x,
      (srcpTraceAligned bs).cell t r x = Fp.ofNat (SrcpGen.cell bs r x) := by
    intro r hr x
    by_cases hx : x < SrcpV3.width
    · exact rowsTrace_mkTab _ _ _ t r x hr hx
    · rw [SrcpGen.cell_high bs r x (by omega)]
      unfold srcpTraceAligned rowsTrace
      dsimp only
      congr 1
      simp only [mkTab, Array.getD_eq_getD_getElem?, Array.getElem?_map]
      cases (Array.range _)[r]? <;> simp [show ¬ x < SrcpV3.width by omega]
  exact ⟨SrcpGen.table_local_at h ⟨hh.2.1, hh.2.2.1⟩ hh.1 hc,
    SrcpGen.table_traffic h hh.1 hc, hh.2.2.2⟩

/-- The same, from the used source proofs themselves (`ProofInputsOk`: the claim-derived
roots with their decoded witness proof entries, `Rcpt/Render/Srcp/ProofInputWf.lean`). -/
theorem srcp_proofs_aligned_complete (xs : List SrcpGen.ProofInput) (h : SrcpGen.ProofInputsOk xs)
    (t : Nat) (pub : List Fp) :
    TableLocal SrcpV3.table (srcpTraceAligned (SrcpGen.blocksOfProofs xs)) t pub ∧
    TableTraffic SrcpV3.interactions (srcpTraceAligned (SrcpGen.blocksOfProofs xs)) t pub
      (srcpTraffic (SrcpGen.blocksOfProofs xs)) ∧
    (srcpTraceAligned (SrcpGen.blocksOfProofs xs)).log t % 3 = 1 :=
  srcp_aligned_complete _ (SrcpGen.blocksOfProofs_wf h) t pub

end ZkFormal.NearV3.Render
