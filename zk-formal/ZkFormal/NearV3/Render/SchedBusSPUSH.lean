import ZkFormal.NearV3.Render.SchedBusSsdSinc
import ZkFormal.NearV3.Render.SchedBusRunGlue
import ZkFormal.NearV3.Render.SchedBusProc
import ZkFormal.NearV3.Render.SchedBusMem

/-!
# `SPUSH` (bus 44): pushes balance

The scan rows (12) send one initial push per converted request, the process rows (13) send the
re-pushes and receive every bucket entry; per run the pushes are a permutation of the bucket
entries (`SchedRun.run_spush_fp`).  **`RenderBundleV3.balancedAt_spush`**.
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render.Ssd ZkFormal.NearV3.Assembly.CodecDigest

theorem count_flatMap_app2 {α β : Type} [BEq β] (l : List α) (f g : α → List β) (m : β) :
    (l.flatMap (fun a => f a ++ g a)).count m = (l.flatMap f).count m + (l.flatMap g).count m := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.count_append] at *; omega

theorem push_msg (R : Run) (c : CReq) : F (pushMsg R c) = SchedRun.pushF R.tau (SchedRun.initPush c) := by
  simp only [F, pushMsg, SchedRun.pushF, SchedRun.initPush, ProcBus.nf, b2n, beq_iff_eq, Nat.mul_comm]

theorem dist_spush (b : NativeBlock) : distPart (fun row => spushM (fx row)) b = [] :=
  (dist_ops (ProcPreparedSequence.input b.pub b.old) b.run).2.2

end ZkFormal.NearV3.Render.SsdBus

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Render.SsdBus ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Candidates NearSpec

theorem covers_spush_send : Covers Sched.B_SPUSH true (fun t => t == 12 || t == 13) = true := by decide +kernel
theorem covers_spush_recv : Covers Sched.B_SPUSH false (fun t => t == 13) = true := by decide +kernel
theorem pub_spush (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub Sched.B_SPUSH s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

/-- **`SPUSH` balance** of a bundle whose tables 12 and 13 are the scan/distribute and process renders
of the `PriorCore` blocks. -/
theorem balancedAt_spush {pub : List Fp} (R : RenderBundleV3 pub) {cb : Bytes} {hint : NearSpecV3.Hint}
    {p : NearSpecV3.Prep} (hp : NearSpecV3.prepD0 cb hint = .ok p) {bs : List NativeBlock}
    (hc : PriorCore p NearSpecV3.B0 bs)
    (h12 : (R ⟨12, by decide⟩).tr = ProcScanDistPhases.trace bs)
    (h13 : (R ⟨13, by decide⟩).tr = procTraceV3 (bs.map NativeBlock.run)) :
    R.BalancedAt Sched.B_SPUSH := by
  intro m
  rw [R.sum_tables true _ m _ covers_spush_send, R.sum_tables false _ m _ covers_spush_recv, pub_spush, pub_spush]
  have hf1 : (List.range 25).filter (fun t => t == 12 || t == 13) = [12, 13] := by decide
  have hf2 : (List.range 25).filter (fun t => t == 13) = [13] := by decide
  rw [hf1, hf2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [R.cnt_tf 12 (by decide) true, R.cnt_tf 13 (by decide) true, R.cnt_tf 13 (by decide) false, h12, h13]
  have i12 : nearAirV3.tables[12].interactions = ScanDist.table.interactions := rfl
  have i13 : nearAirV3.tables[13].interactions = Proc.tableB.interactions := rfl
  have hcap := (prior_run_capacities hp _ bs hc).2
  rw [i12, i13, ssd_count hp bs hc _ true spushM row_spush (by simp [spushM, fp_01]) 12 pub m,
    ssd_blocks bs (fun b hb => (hc.valid b hb).2), ProcBus.count_pushS _ (by omega),
    ProcBus.count_pushR _ (by omega)]
  simp only [List.flatMap_map]
  have hd : bs.flatMap (distPart fun row => spushM (fx row)) = [] := by
    simp [dist_spush]
  rw [hd, List.append_nil]
  have hperm : (bs.flatMap fun b => (scanPart (fun row => spushM (fx row)) b ++ ProcBus.pushSL b.run)).Perm
      (bs.flatMap fun b => ProcBus.pushRL b.run) := by
    apply Cdc.flatMap_perm'
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    have hr := (hc.indexed i b hi).1.2
    rw [scan_spush, List.map_congr_left (fun c _ => push_msg b.run c)]
    have := SchedRun.run_spush_fp _ _ _ hr
    rwa [List.map_map] at this
  have h := hperm.count_eq m
  rw [count_flatMap_app2] at h
  omega

end RenderBundleV3
end ZkFormal.NearV3.Assembly
