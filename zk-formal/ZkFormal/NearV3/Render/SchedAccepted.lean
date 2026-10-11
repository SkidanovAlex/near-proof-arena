import ZkFormal.NearV3.Render.BundleSched
import ZkFormal.NearV3.Assembly.SchedulerRunMemoryLocal
import ZkFormal.NearV3.Assembly.SchedulerRunCodecComparisons
import ZkFormal.NearV3.Candidates.ProcDistComparisonValid

/-!
# Scheduler tables 12–15 from one accepted witness, on one block list

`sched_renders_accepted`: for `checkD0a B0 cb wb = .ok ()` there is one native block list
`bs` (`PriorCore p B0 bs`, the comparator facts of its codec outputs included) with renders of

* table 12 (`ScanDist.table`, `Ssd.ssd_v3_aligned_complete`),
* table 13 (`Proc.tableB`, all runs, `procRenderV3`),
* table 14 (`Mem.table`, all runs: `memAllRenderV3` — `prior_memory_table` + the row traffic of
  `MemConcatCells.trace`),
* table 15 (the comparator, `cmpRenderV3` over `ProcNativeOldComparisonCapacity.requests bs` =
  every run's memory/process comparisons, the codec comparisons and the distribute comparisons;
  each `CmpOk` from acceptance, at most `2,936,832` requests),

with their traces and traffics named, so the bus balances can be stated on them.
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Assembly
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpec NearSpecV3
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Candidates

/-- Cell `c` of row `r` of the concatenated memory table of all runs. -/
def memAllCell (rs : List Run) (r c : Nat) : Nat := Complete.natCell (MemConcatCells.rows rs) Complete.memPad r c

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem mem_interactions_current :
    Mem.interactions.all (fun i => i.exprs.all ZkFormal.NearV3.Candidates.ShaHeight.currentOnly) = true := by
  decide +kernel

theorem mem_currentOnly : CurrentOnly Mem.table.interactions := by
  intro i hi e he
  exact List.all_eq_true.mp (List.all_eq_true.mp mem_interactions_current i hi) e he

/-- Table 14 over all runs of the native blocks. -/
def memAllRenderV3 (pub : List Fp) {cb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint = .ok p)
    {B : Nat} (bs : List NativeBlock) (hc : PriorCore p B bs) : TableRenderV3 pub 14 (by decide) where
  tr := MemConcatCells.trace (bs.map NativeBlock.run)
  tf := rowsTraffic Mem.table.interactions (memAllCell (bs.map NativeBlock.run)) 22 14 pub
  loc := prior_memory_table hp B bs hc 14 pub
  traffic := rowFn_traffic _ mem_currentOnly _ _ 14 22 pub rfl (fun _ _ _ => rfl)
  aligned := show 22 % 3 = 1 from rfl

/-- Every comparison of the frozen scheduler family is well-formed (from acceptance). -/
theorem old_requests_ok {cb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint = .ok p) {B : Nat}
    (bs : List NativeBlock) (hc : PriorCore p B bs) (hcodec : ∀ b ∈ bs, ∀ q ∈ b.output.cmps, Complete.CmpOk q) :
    ∀ q ∈ ProcNativeOldComparisonCapacity.requests bs, Complete.CmpOk q := by
  intro q hq
  unfold ProcNativeOldComparisonCapacity.requests ProcNativeOldComparisonBudget.requests at hq
  obtain ⟨b, hb, hq⟩ := List.mem_flatMap.mp hq
  rcases List.mem_append.mp hq with hq | hq
  · rcases List.mem_append.mp hq with hq | hq
    · exact prior_core_run_comparisons p B bs hc b hb q hq
    · exact hcodec b hb q hq
  · exact ProcDistComparisonValid.prior_core hp bs hc b hb q hq

/-- **Tables 12–15 from acceptance, on one native block list.** -/
theorem sched_renders_accepted {cb wb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint = .ok p)
    {k : WalkD0} {w : StateWitness} (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w)
    (h : checkD0a B0 cb wb = .ok ()) (pub : List Fp) :
    ∃ bs : List NativeBlock, PriorCore p B0 bs ∧
      ∃ (R12 : TableRenderV3 pub 12 (by decide)) (R13 : TableRenderV3 pub 13 (by decide))
        (R14 : TableRenderV3 pub 14 (by decide)) (R15 : TableRenderV3 pub 15 (by decide)),
      R12.tr = ProcScanDistPhases.trace bs ∧
      R12.tf = rowsTraffic ScanDist.table.interactions (Ssd.ssdCell bs) 22 12 pub ∧
      R13.tr = procTraceV3 (bs.map NativeBlock.run) ∧
      R13.tf = rowsTraffic Proc.tableB.interactions (procCell (bs.map NativeBlock.run)) 22 13 pub ∧
      R14.tr = MemConcatCells.trace (bs.map NativeBlock.run) ∧
      R14.tf = rowsTraffic Mem.table.interactions (memAllCell (bs.map NativeBlock.run)) 22 14 pub ∧
      R15.tr = cmpTraceAligned (ProcNativeOldComparisonCapacity.requests bs) ∧
      R15.tf = cmpTraffic (ProcNativeOldComparisonCapacity.requests bs) := by
  obtain ⟨bs, hc, _, hcodec⟩ := accepted_run_codec_comparisons hp hk hw h (by decide)
  have hok := old_requests_ok hp bs hc hcodec
  have hlen := (ProcNativeOldComparisonCapacity.native_bound hp bs hc).1
  refine ⟨bs, hc, ssdRenderV3 pub hp bs hc, ?_, memAllRenderV3 pub hp bs hc,
    cmpRenderV3 pub _ hok (by omega), rfl, rfl, ?_⟩
  · refine procRenderV3 pub (bs.map NativeBlock.run) ?_ ?_ ?_ (prior_run_capacities hp _ bs hc).2
    · intro R hR
      obtain ⟨sp, prev, hs, hr, _⟩ := prior_run_data hp _ bs hc R hR
      exact ⟨ProcPreparedSequence.input sp prev, hs.params, hr⟩
    · intro R rest he
      exact prior_run_index p _ bs hc 0 R (by rw [he]; rfl)
    · intro pre R S post he
      have hR : R.tau = pre.length := prior_run_index p _ bs hc pre.length R (by
        rw [he, List.getElem?_append_right (by omega)]
        simp)
      have hS : S.tau = pre.length + 1 := prior_run_index p _ bs hc (pre.length + 1) S (by
        rw [he, List.getElem?_append_right (by omega)]
        simp)
      omega
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end ZkFormal.NearV3.Render
