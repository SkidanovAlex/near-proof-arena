import ZkFormal.NearV3.Render.SchedAccepted

/-!
# The comparator bus `B_SCMP` on the accepted renders, up to the codec's sends

`scmp_balance_core`: on the renders of `sched_renders_accepted` (same block list `bs`), the
comparisons sent by the memory table (14), the process table (13) and the scan/distribute table (12),
together with the codec outputs' comparisons `bs.flatMap (·.output.cmps)`, are exactly the
comparisons received by the comparator table (15).  The SCMP balance of the bundle therefore reduces
to one codec fact: the codec table's `B_SCMP` sends are `(bs.flatMap (·.output.cmps)).map cmpMsg`.
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Assembly
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpec NearSpecV3
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Candidates

theorem count_flatMap3 (bs : List NativeBlock) (f g h : NativeBlock → List (Nat × Nat × Nat)) (m : List Fp) :
    ((bs.flatMap (fun b => f b ++ g b ++ h b)).map Complete.cmpMsg).count m =
      ((bs.flatMap f).map Complete.cmpMsg).count m + ((bs.flatMap g).map Complete.cmpMsg).count m +
      ((bs.flatMap h).map Complete.cmpMsg).count m := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.map_append, List.count_append] at *
    omega

theorem proc_count_congr (rs : List Run) (t : Nat) (pub msg : List Fp) :
    tableBusCount Proc.tableB.interactions (procTraceV3 rs) t pub B_SCMP true msg =
      tableBusCount ProcBoundaryRepair.table.interactions (ProcConcatGeometry.trace rs) t pub B_SCMP true msg := by
  have hcells : ∀ r, r < 2 ^ 22 → ∀ c, (procTraceV3 rs).cell t r c = Fp.ofNat (procCell rs r c) :=
    fun r hr c => rowsTrace_cells 22 _ _ (fun r c h => pv_cell_ge _ c h) t r hr c
  have hl : (ProcConcatGeometry.trace rs).log t = (procTraceV3 rs).log t := rfl
  have hc : ∀ r, r < (ProcConcatGeometry.trace rs).height t → ∀ c,
      (ProcConcatGeometry.trace rs).cell t r c = (procTraceV3 rs).cell t r c := by
    intro r hr c
    rw [hcells r hr c]; rfl
  exact (tableBusCount_congr_rows hl hc _ pub B_SCMP true msg).symm

theorem cmp_recv_count (cmps : List (Nat × Nat × Nat)) (hrows : cmps.length ≤ 2 ^ 22) (t : Nat)
    (pub msg : List Fp) :
    tableBusCount (Cmp.table B_SCMP).interactions (cmpTraceAligned cmps) t pub B_SCMP false msg =
      (cmps.map Complete.cmpMsg).count msg := by
  have hl : (CmpHeight.trace cmps).log t = (cmpTraceAligned cmps).log t := rfl
  have hc := schedTraceAligned_cells (Gen.Cmp.rows cmps) (fun _ => Gen.Cmp.padRow) t
  rw [← tableBusCount_congr_rows hl hc]
  show tableBusCount (Cmp.interactions B_SCMP) (CmpHeight.trace cmps) t pub B_SCMP false msg = _
  rw [CmpHeight.cmp_count cmps B_SCMP t pub msg false hrows]
  simp only [ite_true]
  rw [Complete.fmsgs_expected]

/-- **`B_SCMP` on tables 12–15, up to the codec's sends.** -/
theorem scmp_balance_core {cb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint = .ok p) {B : Nat}
    (bs : List NativeBlock) (hc : PriorCore p B bs) (t12 t13 t14 t15 : Nat) (pub msg : List Fp) :
    tableBusCount Mem.interactions (MemConcatCells.trace (bs.map NativeBlock.run)) t14 pub B_SCMP true msg +
    tableBusCount Proc.tableB.interactions (procTraceV3 (bs.map NativeBlock.run)) t13 pub B_SCMP true msg +
    tableBusCount ScanDist.table.interactions (ProcScanDistPhases.trace bs) t12 pub B_SCMP true msg +
    ((bs.flatMap (fun b => b.output.cmps)).map Complete.cmpMsg).count msg =
    tableBusCount (Cmp.table B_SCMP).interactions
      (cmpTraceAligned (ProcNativeOldComparisonCapacity.requests bs)) t15 pub B_SCMP false msg := by
  have hlen := (ProcNativeOldComparisonCapacity.native_bound hp bs hc).1
  rw [cmp_recv_count _ (by omega), proc_count_congr, prior_run_comparison_count hp B bs hc,
    ProcScanDistPhases.count hp bs hc]
  unfold ProcNativeOldComparisonCapacity.requests ProcNativeOldComparisonBudget.requests
  rw [count_flatMap3]
  omega

end ZkFormal.NearV3.Render
