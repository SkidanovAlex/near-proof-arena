import ZkFormal.NearV3.Assembly.RenderV3RcptLayout
import ZkFormal.NearV3.Assembly.RcptRoutingRowLocal
import ZkFormal.NearV3.Assembly.RcptRoutingCells
import ZkFormal.NearV3.Assembly.RcptRoutingCommute
import ZkFormal.NearV3.Assembly.RcptEntityFlags
import ZkFormal.NearV3.Assembly.RcptEntityOtherLocal
import ZkFormal.NearV3.Assembly.RcptSegmentTokenBytes
import ZkFormal.NearV3.Assembly.RoutingSelectedColumns
import ZkFormal.NearV3.Assembly.RcptRoutingNativeSelection

/-!
# BND coverage of the honest receipt trace (whole-trace routing identification)

Every row of the honest receipt trace `rcptTraceNative pub x` whose boundary gate `gBd` is set
is a routing-active coordinate (`sV`, or `sRID` index 0) of a planned receipt `p` of `x.lists`
(padding and list-header rows have `gBd = 0`), and its boundary key is
`routeKey (bounded intervals) (nativeRoutingIndex k p) (routingPosition p row)`
(`native_boundary_key`).  For an accepted witness (`AcceptedV3`) every such key is a row of the
bounded boundary table (`native_routing_selected`), which is `A.bnds` — so the coverage premise
of `honest_bnd_balance` holds (`AcceptedV3.bnd_coverage`) and the BND bus balances with no
premise (`RcptBal.bnd_balanced_accepted`).
-/

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open RoutingBoundedLayout

/-- A planned receipt row belongs to a receipt of the lists, and `sV` rows index the receiver. -/
theorem planned_receipt_facts {lists : List (List Input)} {p : ReceiptPlan} {row : Coord}
    (h : PlannedRow.receipt p row ∈ plannedRows lists) :
    p.input.receipt ∈ lists.flatten.map Input.receipt ∧
      (row.state = sV → row.index < p.input.receipt.receiverId.length) := by
  rw [← plannedSegments_rows] at h
  obtain ⟨seg, hs, hm⟩ := List.mem_flatMap.mp h
  cases seg with
  | header lp =>
    obtain ⟨c, -, he⟩ := List.mem_map.mp hm
    cases he
  | receipt rp s =>
    obtain ⟨c, hc, he⟩ := List.mem_map.mp hm
    simp only [SegmentPlan.wrap, PlannedRow.receipt.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hin := List.mem_of_getElem? (plannedSegment_receipt_input lists rp s hs)
    refine ⟨hin, fun hv => ?_⟩
    obtain ⟨hst, hidx, -⟩ := segment_member hc
    simp only [SegmentPlan.state] at hst
    simp only [SegmentPlan.length] at hidx
    rw [← hst, hv] at hidx
    simpa [fieldLen, sV, sCL, sPL, sP, sVL] using hidx

section
variable (pub : List Fp) (x : RcptInput)

/-- The routing-rest aux of the honest receipt trace (everything below the routing layer, with
the outer layers commuted inside). -/
def routingRest : ReceiptPlan → Coord → Nat → Fp :=
  digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux (systemAux
    (keyAux x.accountId x.accessId (gasBorrowAux x.ctx (gasEffectiveAux x.ctx
      (candidateGasDelayAux x.ctx (gasFlagAux x.ctx (gasTokenAux (receiptPlanToken x.ctx x.lists)
        (gasProductAux x.ctx (depositFinalAux (depositPlanPrevious x.lists) (depositPlanAccount x.steps)
          x.fallback)))))))))))))

theorem complete_aux_routing :
    completeReceiptAux x.ctx x.k x.lists x.accountId x.accessId
        (depositFinalAux (depositPlanPrevious x.lists) (depositPlanAccount x.steps) x.fallback) =
      routingAux (nativeRoutingInterval x.k) (routingRest x) := by
  simp only [completeReceiptAux, routingRest, ← routing_system_commute, ← routing_named_commute,
    ← routing_predecessor_commute, ← routing_length_commute, ← routing_character_commute,
    ← routing_digest_commute]

/-- Receipt-row cells of the honest trace (non-emission columns). -/
theorem native_receipt_cell {pos : Nat} {p : ReceiptPlan} {row : Coord}
    (ha : (plannedRows x.lists)[pos]? = some (.receipt p row)) (col : Nat)
    (hcol : emissionColumn col = false) :
    (rcptTraceNative pub x).cell 0 pos col =
      receiptCell (booleanConstants (completeReceiptConstants x.ctx x.k x.accountId
          (depositConstants (depositPlanAccount x.steps) (depositAgeConstants (depositPlanPrevious x.lists) x.constants))))
        (tokenReceiptAux pub (nativeDigests x.ctx x.digests) (receiptPlanToken x.ctx x.lists)
          (booleanReceiptAux (routingAux (nativeRoutingInterval x.k) (routingRest x)))) p row col := by
  unfold rcptTraceNative
  rw [booleanReceiptTrace_planned_cell _ _ _ _ _ _ _ _ _ _ _ ha col hcol, ← complete_aux_routing]
  rfl

theorem native_q_cell {pos : Nat} {p : ReceiptPlan} {row : Coord}
    (ha : (plannedRows x.lists)[pos]? = some (.receipt p row)) :
    (rcptTraceNative pub x).cell 0 pos q = Fp.ofNat (nativeRoutingIndex x.k p.input.receipt) := by
  rw [native_receipt_cell pub x ha q (by decide)]
  have hqb : q ∉ boolCols := by decide
  have hqr : q ∈ rconsts := by decide
  have hq29 : ¬ q ≤ 29 := by decide
  simp only [receiptCell, booleanConstants, boolInput, hqb, hqr, hq29, if_false, if_true,
    show q ≠ rf by decide, show q ≠ rl by decide, show q ≠ lastR by decide, show q ≠ le by decide,
    show q ≠ j by decide, show q ≠ nj by decide, show q ≠ r by decide, show q ≠ cj by decide,
    show q ≠ o by decide, show q ≠ oEnd by decide, show q ≠ o2 by decide, show q ≠ o2End by decide,
    show (q = Lp || q = Lv || q = Ls || q = kt || q = hr) = false by decide,
    completeReceiptConstants, nativePriceConstants, systemConstants, systemIdentityConstants,
    keyConstants, nativeRoutingConstants, show q ≠ ge by decide, show q ≠ sys by decide,
    show q ≠ ee by decide, show q ≠ dm by decide, show q ≠ dd by decide, show q ≠ kslot by decide,
    Bool.false_eq_true, ite_false, ite_true]

theorem native_gate_inactive {pos : Nat} {p : ReceiptPlan} {row : Coord}
    (ha : (plannedRows x.lists)[pos]? = some (.receipt p row)) (hr : routingActive row = false) :
    (rcptTraceNative pub x).cell 0 pos gBd = 0 := by
  rw [native_receipt_cell pub x ha gBd (by decide)]
  exact (routing_inactive_cells _ _ _ _ _ _ p row hr).2.2

theorem native_scratch_active {pos : Nat} {p : ReceiptPlan} {row : Coord}
    (ha : (plannedRows x.lists)[pos]? = some (.receipt p row)) (hr : routingActive row = true)
    (col : Nat) (hc : routingScratch col = true) :
    (rcptTraceNative pub x).cell 0 pos col =
      frameCell (receiptRoutingFrame (nativeRoutingInterval x.k) p row) col := by
  rw [native_receipt_cell pub x ha col (by
    have := routingScratch_bounds col hc
    simp only [emissionColumn, decide_eq_false_iff_not]
    omega)]
  exact routingAux_transport _ _ _ _ _ _ p row col hr hc

theorem native_gate_header {pos : Nat} {lp : ListPlan} {row : Coord}
    (ha : (plannedRows x.lists)[pos]? = some (.header lp row)) :
    (rcptTraceNative pub x).cell 0 pos gBd = 0 := by
  unfold rcptTraceNative
  rw [booleanReceiptTrace_planned_cell _ _ _ _ _ _ _ _ _ _ _ ha gBd (by decide)]
  simp [plannedCell, headerCell, headerStreamAux, tokenHeaderAux, emissionHeaderFallback,
    booleanHeaderAux, boolInput, completeReceiptHeaders, digestHeaderMetadata, characterHeaderAux,
    systemHeaderAux, routingHeaderAux, gBd, rf, rl, lastR, le, j, nj, r, cj, oEnd, o2, o2End, reg, b,
    tok, hr, gDg, gV, gS]

theorem native_gate_padding {pos : Nat} (ha : (plannedRows x.lists)[pos]? = none) :
    (rcptTraceNative pub x).cell 0 pos gBd = 0 := by
  unfold rcptTraceNative
  exact booleanReceiptTrace_padding _ _ _ _ _ _ _ _ _ _ ha gBd

/-- **Whole-trace identification of the boundary lookups.** -/
theorem native_boundary_rows {pos : Nat}
    (hg : (rcptTraceNative pub x).cell 0 pos gBd = 1) :
    ∃ p row, (plannedRows x.lists)[pos]? = some (.receipt p row) ∧ routingActive row = true := by
  cases ha : (plannedRows x.lists)[pos]? with
  | none =>
    rw [native_gate_padding pub x ha] at hg
    exact absurd hg (by decide)
  | some a =>
    cases a with
    | header lp row =>
      rw [native_gate_header pub x ha] at hg
      exact absurd hg (by decide)
    | receipt p row =>
      cases hr : routingActive row with
      | false =>
        rw [native_gate_inactive pub x ha hr] at hg
        exact absurd hg (by decide)
      | true => exact ⟨p, row, rfl, hr⟩

/-- The boundary key of a routing-active receipt row of the honest trace. -/
theorem native_boundary_key {pos : Nat} {p : ReceiptPlan} {row : Coord}
    (ha : (plannedRows x.lists)[pos]? = some (.receipt p row)) (hr : routingActive row = true)
    (hi : nativeRoutingIndex x.k p.input.receipt < 128) (hp : routingPosition p row < 65) :
    RoutingQCandidate.physicalBoundaryKey (rcptTraceNative pub x) 0 pos =
      routeKey (boundedIntervals x.k.L x.k.H.shardId) (nativeRoutingIndex x.k p.input.receipt)
        (routingPosition p row) := by
  rw [← routeColumns_key (boundedIntervals x.k.L x.k.H.shardId) _ _ hi hp (rcptTraceNative pub x) 0 pos]
  have hs := native_scratch_active pub x ha hr
  have cq := native_q_cell pub x ha
  have ci := hs iB (by decide)
  have cl := hs loB (by decide)
  have ch := hs hiB (by decide)
  have cn := hs hnB (by decide)
  simp only [RoutingQCandidate.physicalBoundaryKey, routedColumnsTrace, routeColumns]
  simp only [frameCell, receiptRoutingFrame, frameOf] at ci cl ch cn
  simp only [q, iB, loB, hiB, hnB, iL, iH, sV, sRID, fs, idx, Lv, b, vB] at cq ci cl ch cn ⊢
  simp only [Nat.reduceEqDiff, decide_true, decide_false, Bool.or_false, Bool.false_or, Bool.or_true,
    Bool.true_or, Bool.false_eq_true, ite_true, ite_false] at ci cl ch cn ⊢
  rw [cq, ci, cl, ch, cn]
  rfl

end

end ZkFormal.NearV3.Assembly.RcptSkeleton

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3
open RoutingBoundedLayout RcptSkeleton

namespace AcceptedV3

variable {cb wb : Bytes} (A : AcceptedV3 cb wb)

/-- **BND coverage**: every physical routing key of the honest receipt trace is a row of the
honest boundary table. -/
theorem bnd_coverage :
    ∀ r ∈ RoutingQCandidate.physicalActiveRows (rcptTraceNative A.pub A.rcptInput) 0,
      RoutingQCandidate.physicalBoundaryKey (rcptTraceNative A.pub A.rcptInput) 0 r ∈
        A.bnds.map BndE.rec4 := by
  intro pos hpos
  simp only [RoutingQCandidate.physicalActiveRows, List.mem_filter, decide_eq_true_eq] at hpos
  obtain ⟨p, row, ha, hr⟩ := native_boundary_rows A.pub A.rcptInput hpos.2
  have hmem : PlannedRow.receipt p row ∈ plannedRows A.rcptInput.lists := List.mem_of_getElem? ha
  obtain ⟨hin, hsv⟩ := planned_receipt_facts hmem
  have happ : p.input.receipt ∈ appliedReceipts A.k A.w := by
    have h := A.lists_applied
    change p.input.receipt ∈ A.lists.flatten.map Input.receipt at hin
    rwa [h] at hin
  obtain ⟨hidx, -, -, hkeys⟩ := native_routing_selected A.hp A.hk A.hd p happ
  -- the receiver is a valid account id (≤ 64 bytes)
  have hwf : p.input.receipt.wf = true := by
    obtain ⟨y, hy, hye⟩ := List.mem_map.mp hin
    obtain ⟨xs, hxs, hyx⟩ := List.mem_flatten.mp hy
    rw [← hye]
    exact A.rcptOk.wf xs hxs y hyx
  have hlen : p.input.receipt.receiverId.length ≤ 64 := by
    simp only [Receipt.wf, AccountId.valid, Bool.and_eq_true, decide_eq_true_eq] at hwf
    grind only
  have hposle : routingPosition p row ≤ p.input.receipt.receiverId.length := by
    unfold routingPosition
    split
    · exact Nat.le_of_lt (hsv (by assumption))
    · exact Nat.le_refl _
  rw [native_boundary_key A.pub A.rcptInput ha hr hidx (by omega)]
  have hrec := RoutingBoundedLayout.boundaryEntries_records (boundedPrep A.p A.k.L A.k.H.shardId)
    (RoutingQCandidate.physicalBoundaryKeys (rcptTraceNative A.pub A.rcptInput) 0)
  unfold bnds bounds
  rw [hrec]
  exact hkeys _ hposle

end AcceptedV3

namespace RcptBal

variable {cb wb : Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)

/-- **BND** for an accepted witness, premise-free. -/
theorem bnd_balanced_accepted (h16 : R.tf 16 = rcptTrafficB A.pub A.rcptInput)
    (h19 : R.tf 19 = bndTraffic A.bnds) : BusBalanced R B_BND :=
  bnd_balanced A R h16 h19 A.bnd_coverage

end RcptBal

end ZkFormal.NearV3.Assembly
