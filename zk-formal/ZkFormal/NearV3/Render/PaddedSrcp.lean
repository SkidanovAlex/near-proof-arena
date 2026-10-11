import ZkFormal.NearV3.Render.Padded
import ZkFormal.NearV3.Rcpt.Render.Srcp.LocalProof
import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficProof
import ZkFormal.NearV3.Rcpt.Render.Srcp.ProofComplete
import ZkFormal.NearV3.Rcpt.Render.SizeRender
import ZkFormal.NearV3.Rcpt.Extract.Srcp.Depth
import ZkFormal.NearV3.Render.ColAgree

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

def srcpTraceBase (bs : List SrcpB) : Trace Fp :=
  let log := padLog22 (logOf (SrcpGen.R bs))
  rowsTrace log (mkTab (2 ^ log) SrcpV3.width (SrcpGen.cell bs))

/-- Completeness of the pre-A10 rows for the base table `SrcpV3.table` (the 56 original
columns); `srcp_aligned_complete` adds the depth columns.  At the aligned height (within its cap `22`), with
exactly the view's traffic `srcpTraffic bs`. -/
theorem srcp_base_complete (bs : List SrcpB) (h : SrcpWf bs) (t : Nat) (pub : List Fp) :
    TableLocal SrcpV3.table (srcpTraceBase bs) t pub ∧
    TableTraffic SrcpV3.interactions (srcpTraceBase bs) t pub (srcpTraffic bs) ∧
    (srcpTraceBase bs).log t % 3 = 1 := by
  have hR : SrcpGen.R bs ≤ 2 ^ 22 := by rw [SrcpGen.R_eq]; exact h.rows
  have hh := padded_log_fits (SrcpGen.R bs) hR
  have hc : ∀ r, r < (srcpTraceBase bs).height t → ∀ x,
      (srcpTraceBase bs).cell t r x = Fp.ofNat (SrcpGen.cell bs r x) := by
    intro r hr x
    by_cases hx : x < SrcpV3.width
    · exact rowsTrace_mkTab _ _ _ t r x hr hx
    · rw [SrcpGen.cell_high bs r x (by omega)]
      unfold srcpTraceBase rowsTrace
      dsimp only
      congr 1
      simp only [mkTab, Array.getD_eq_getD_getElem?, Array.getElem?_map]
      cases (Array.range _)[r]? <;> simp [show ¬ x < SrcpV3.width by omega]
  exact ⟨SrcpGen.table_local_at h ⟨hh.2.1, hh.2.2.1⟩ hh.1 hc,
    SrcpGen.table_traffic h hh.1 hc, hh.2.2.2⟩

/-- The same, from the used source proofs themselves (`ProofInputsOk`: the claim-derived
roots with their decoded witness proof entries, `Rcpt/Render/Srcp/ProofInputWf.lean`). -/
theorem srcp_proofs_base_complete (xs : List SrcpGen.ProofInput) (h : SrcpGen.ProofInputsOk xs)
    (t : Nat) (pub : List Fp) :
    TableLocal SrcpV3.table (srcpTraceBase (SrcpGen.blocksOfProofs xs)) t pub ∧
    TableTraffic SrcpV3.interactions (srcpTraceBase (SrcpGen.blocksOfProofs xs)) t pub
      (srcpTraffic (SrcpGen.blocksOfProofs xs)) ∧
    (srcpTraceBase (SrcpGen.blocksOfProofs xs)).log t % 3 = 1 :=
  srcp_base_complete _ (SrcpGen.blocksOfProofs_wf h) t pub

/-! ## The A10 depth columns (`SrcpV3.tableD`) -/

namespace SrcpGen

/-- The depth slack `DP0 − |path|` on a block's root row, `0` elsewhere. -/
def depthVal (bs : List SrcpB) (pos : Nat) : Nat :=
  if pos < R bs then
    match (recs bs).getD pos default with
    | (i, .root) => SrcpV3.DP0 - (bs.getD i default).path.length
    | _ => 0
  else 0

/-- The honest rows of `SrcpV3.tableD`: the base rows plus the slack bits `db_e`. -/
def cellD (bs : List SrcpB) (pos x : Nat) : Nat :=
  if x < SrcpV3.width then cell bs pos x
  else if x < SrcpV3.widthD then (depthVal bs pos / 2 ^ (x - SrcpV3.width)) % 2 else 0

theorem cellD_low (bs : List SrcpB) (r : Nat) {x : Nat} (hx : x < SrcpV3.width) :
    cellD bs r x = cell bs r x := by
  unfold cellD; rw [if_pos hx]

theorem recs_fst_lt (bs : List SrcpB) {pos : Nat} (hp : pos < R bs) :
    ((recs bs).getD pos default).1 < bs.length := by
  have hm : (recs bs).getD pos default ∈ recs bs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by unfold R at hp; exact hp)]
    exact List.getElem_mem _
  simp only [recs, List.mem_flatMap, List.mem_range, List.mem_map] at hm
  obtain ⟨i, hi, k, -, he⟩ := hm
  rw [show (recs bs).getD pos default = (i, k) from he.symm]; exact hi

/-- A generated row with `rt = 1` is a block's root row. -/
theorem root_cells (bs : List SrcpB) {pos : Nat} (h1 : cell bs pos SrcpV3.rt = 1) :
    ∃ i, i < bs.length ∧ cell bs pos SrcpV3.q = (bs.getD i default).ql - 1 ∧
      cell bs pos SrcpV3.qe = (bs.getD i default).qe ∧
      depthVal bs pos = SrcpV3.DP0 - (bs.getD i default).path.length := by
  unfold cell at h1
  split at h1
  · rename_i hp
    have hi := recs_fst_lt bs hp
    generalize hr : (recs bs).getD pos default = p at h1 hi
    obtain ⟨i, k⟩ := p
    cases k with
    | root =>
      refine ⟨i, hi, ?_, ?_, ?_⟩
      · unfold cell; rw [if_pos hp, hr]; simp [rowFrame, frame, rootFrame, Frame.cell, SrcpV3.q]
      · unfold cell; rw [if_pos hp, hr]; simp [rowFrame, frame, rootFrame, Frame.cell, SrcpV3.qe]
      · unfold depthVal; rw [if_pos hp, hr]
    | leaf p => simp [rowFrame, frame, leafFrame, Frame.cell, SrcpV3.rt] at h1
    | path a o => simp [rowFrame, frame, pathFrame, Frame.cell, SrcpV3.rt] at h1
  · simp [SrcpV3.rt, SrcpV3.sz] at h1

theorem ql_pos' {bs : List SrcpB} (h : SrcpWf bs) {i : Nat} (hi : i < bs.length) :
    1 ≤ (bs.getD i default).ql := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  cases i with
  | zero => rw [h.q0 hi]; exact Nat.le_refl 1
  | succ k => rw [h.qnext k hi]; omega

theorem getD_mem (bs : List SrcpB) {i : Nat} (hi : i < bs.length) : bs.getD i default ∈ bs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem _

/-- The A10 constraints hold on the honest rows with depth-bounded blocks. -/
theorem depth_constraints {bs : List SrcpB} (h : SrcpWf bs) (hd : ∀ B ∈ bs, B.path.length ≤ SrcpV3.DP0)
    {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hc : ∀ r, r < tr.height t → ∀ x, x < SrcpV3.widthD → tr.cell t r x = Fp.ofNat (cellD bs r x)) :
    ∀ r, r < tr.height t → ∀ e ∈ SrcpV3.depthConstraints, e.eval tr t r pub = 0 := by
  intro r hr e he
  have hbit : ∀ b, b < 6 → tr.cell t r (SrcpV3.db b) = Fp.ofNat ((depthVal bs r / 2 ^ b) % 2) := by
    intro b hb
    rw [hc r hr _ (by unfold SrcpV3.db SrcpV3.widthD; omega)]
    simp only [cellD, SrcpV3.db, SrcpV3.width, SrcpV3.widthD, show ¬ 56 + b < 56 by omega,
      show 56 + b < 62 by omega, if_false, if_true, Nat.add_sub_cancel_left]
  have hbool : ∀ b, b < 6 → tr.cell t r (SrcpV3.db (0 + b)) = 0 ∨ tr.cell t r (SrcpV3.db (0 + b)) = 1 := by
    intro b hb
    rw [Nat.zero_add, hbit b hb]
    rcases Nat.mod_two_eq_zero_or_one (depthVal bs r / 2 ^ b) with h2 | h2 <;> rw [h2]
    · exact Or.inl rfl
    · exact Or.inr rfl
  simp only [SrcpV3.depthConstraints, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton] at he
  rcases he with ⟨b, hb, rfl⟩ | rfl
  · have := hbool b hb
    rw [Nat.zero_add] at this
    simp only [eval_bool, eval_c]
    rcases this with h0 | h0 <;> rw [h0] <;> grind
  · have hrt : tr.cell t r SrcpV3.rt = Fp.ofNat (cell bs r SrcpV3.rt) := by
      rw [hc r hr _ (by decide)]; simp [cellD, SrcpV3.rt, SrcpV3.width]
    have hb1 := cell_bool_bound bs r SrcpV3.rt (by decide)
    simp only [eval_mul, eval_c, eval_sub, eval_k, hrt]
    rcases (show cell bs r SrcpV3.rt = 0 ∨ cell bs r SrcpV3.rt = 1 by omega) with h0 | h1
    · rw [h0, show Fp.ofNat 0 = 0 from rfl, Lean.Grind.Semiring.zero_mul]
    · obtain ⟨i, hi, hq, hqe, hdv⟩ := root_cells bs h1
      have hB := getD_mem bs hi
      have hlen := hd _ hB
      have hroot := (h.root _ hB).1
      have hql := ql_pos' h hi
      generalize bs.getD i default = B at hq hqe hdv hB hlen hroot hql
      have hbits : SrcpV3.depthBits.eval tr t r pub = ((SrcpV3.DP0 - B.path.length : Nat) : Fp) := by
        rw [show SrcpV3.depthBits = Dsl.bits (fun e => Dsl.c (SrcpV3.db e)) 0 6 from rfl,
          eval_bits tr t r pub SrcpV3.db 0 6 hbool]
        congr 1
        rw [SizeRender.bitsVal_congr _ (fun e => (depthVal bs r / 2 ^ e) % 2) 6 (fun e he => by
            simp only [cv, hbit e he, Fp.toNat_ofNat]
            exact Nat.mod_eq_of_lt (by
              have := Nat.mod_lt (depthVal bs r / 2 ^ e) (show 2 > 0 by decide)
              unfold ZkFormal.Algebra.P; omega)),
          SizeRender.bitsVal_bits, hdv]
        exact Nat.mod_eq_of_lt (by unfold SrcpV3.DP0; omega)
      have cq : tr.cell t r SrcpV3.q = ((B.ql - 1 : Nat) : Fp) := by
        rw [hc r hr _ (by decide), cellD_low bs r (by decide), hq]; rfl
      have cqe : tr.cell t r SrcpV3.qe = ((B.ql + B.path.length : Nat) : Fp) := by
        rw [hc r hr _ (by decide), cellD_low bs r (by decide), hqe, hroot]; rfl
      rw [h1, hbits, cq, cqe]
      have e1 := congrArg (fun n : Nat => (n : Fp)) (show (SrcpV3.DP0 - B.path.length) + B.path.length = SrcpV3.DP0 by omega)
      have e2 := congrArg (fun n : Nat => (n : Fp)) (show (B.ql - 1) + 1 = B.ql by omega)
      simp only [natCast_add] at e1 e2
      rw [natCast_add]
      have : ((1 : Nat) : Fp) = 1 := rfl
      grind

end SrcpGen

/-- Every `SrcpV3.table` expression reads only the 56 base columns. -/
theorem srcp_base_cols : ∀ e ∈ SrcpV3.table.exprs, e.colBound ≤ SrcpV3.width := by
  have hh : (SrcpV3.table.exprs.all fun e => decide (e.colBound ≤ SrcpV3.width)) = true := by
    decide +kernel
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp hh e he)

theorem srcp_base_icols : ∀ i ∈ SrcpV3.interactions, ∀ e ∈ i.mult ++ i.msg, e.colBound ≤ SrcpV3.width :=
  fun i hi e he => srcp_base_cols e (List.mem_append_right _ (List.mem_flatMap.2 ⟨i, hi, he⟩))

def srcpTraceAligned (bs : List SrcpB) : Trace Fp :=
  let log := padLog22 (logOf (SrcpGen.R bs))
  rowsTrace log (mkTab (2 ^ log) SrcpV3.widthD (SrcpGen.cellD bs))

/-- **Source-proof table completeness at the aligned height, with the A10 depth check**
(`SrcpV3.tableD`, cap `22`), with exactly the view's traffic `srcpTraffic bs`.  The
hypotheses are the view's own `SrcpWf bs` and A10 for every block. -/
theorem srcp_aligned_complete (bs : List SrcpB) (h : SrcpWf bs)
    (hd : ∀ B ∈ bs, B.path.length ≤ NearSpecV3.Dp0) (t : Nat) (pub : List Fp) :
    TableLocal SrcpV3.tableD (srcpTraceAligned bs) t pub ∧
    TableTraffic SrcpV3.interactions (srcpTraceAligned bs) t pub (srcpTraffic bs) ∧
    (srcpTraceAligned bs).log t % 3 = 1 := by
  have base := srcp_base_complete bs h t pub
  have hlog : (srcpTraceAligned bs).log t = (srcpTraceBase bs).log t := rfl
  have hcols : ∀ r c, c < SrcpV3.width →
      (srcpTraceAligned bs).cell t r c = (srcpTraceBase bs).cell t r c := by
    intro r c hc
    unfold srcpTraceAligned srcpTraceBase rowsTrace
    dsimp only
    congr 1
    simp only [mkTab, Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases (Array.range _)[r]? <;>
      simp [SrcpGen.cellD, hc, show c < SrcpV3.widthD by unfold SrcpV3.widthD SrcpV3.width at *; omega]
  have hL := tableLocal_congr_cols hlog hcols srcp_base_cols base.1
  have hcD : ∀ r, r < (srcpTraceAligned bs).height t → ∀ x, x < SrcpV3.widthD →
      (srcpTraceAligned bs).cell t r x = Fp.ofNat (SrcpGen.cellD bs r x) :=
    fun r hr x hx => rowsTrace_mkTab _ _ _ t r x hr hx
  exact ⟨SrcpV3.local_of_base hL (SrcpGen.depth_constraints h hd hcD),
    tableTraffic_congr_cols hlog hcols srcp_base_icols base.2.1, base.2.2⟩

/-- The same, from the used source proofs themselves (`ProofInputsOk`) and A10 for them. -/
theorem srcp_proofs_aligned_complete (xs : List SrcpGen.ProofInput) (h : SrcpGen.ProofInputsOk xs)
    (hd : ∀ x ∈ xs, x.entry.proof.path.length ≤ NearSpecV3.Dp0) (t : Nat) (pub : List Fp) :
    TableLocal SrcpV3.tableD (srcpTraceAligned (SrcpGen.blocksOfProofs xs)) t pub ∧
    TableTraffic SrcpV3.interactions (srcpTraceAligned (SrcpGen.blocksOfProofs xs)) t pub
      (srcpTraffic (SrcpGen.blocksOfProofs xs)) ∧
    (srcpTraceAligned (SrcpGen.blocksOfProofs xs)).log t % 3 = 1 := by
  refine srcp_aligned_complete _ (SrcpGen.blocksOfProofs_wf h) ?_ t pub
  intro B hB
  simp only [SrcpGen.blocksOfProofs, List.mem_ofFn] at hB
  obtain ⟨i, rfl⟩ := hB
  simpa [SrcpGen.blockOfProof] using hd _ (List.getElem_mem _)

end ZkFormal.NearV3.Render
