import ZkFormal.NearV3.Render.SchedBusSPUSH

/-!
# `SINC` (bus 43): increases balance

The scan rows (12) send every processed increase `(τ, 64·cid + j, incs[j], |incs| − j − 1, s, r, link)`
once (`req_sinc_block`), the process rows (13) receive one per processed entry; per run these are the
same multiset (`SchedRun.run_sinc_fp`).  **`RenderBundleV3.balancedAt_sinc`**.
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render.Ssd ZkFormal.NearV3.Assembly.CodecDigest

set_option maxRecDepth 8192 in
theorem param_sinc (R : Run) : sincM (fx (Scan.paramRow R)) = [] := by
  simp only [sincM, fx, ProcScanParamPhysical.row_all, ProcScanParamLocal.assignments]
  ssd_eval

set_option maxRecDepth 8192 in
theorem header_sinc (tv n i sv count left : Nat) : sincM (fx (ProcDistHeader.row tv n i sv count left)) = [] := by
  simp only [sincM, fx, ProcDistHeaderPhysical.row_all, ProcDistHeader.assignments]
  ssd_eval

set_option maxRecDepth 8192 in
theorem shard_sinc (tv n sd i x count left budget kp : Nat) :
    sincM (fx (ProcDistShardRow.row tv n sd i x count left budget kp)) = [] := by
  simp only [sincM]
  simp (disch := decide) only [shard_fx, ProcDistShardRow.core]
  ssd_eval

set_option maxRecDepth 8192 in
theorem cell_sinc (ids : List Nat) (tv n i j sv rr n1 l1 n2 l2 : Nat) (al : Bool) :
    sincM (fx (ProcDistCellRow.row ids tv n i j sv rr n1 l1 n2 l2 al)) = [] := by
  simp only [sincM]
  simp (disch := decide) only [cell_fx, ProcDistCellRow.core]
  ssd_eval

theorem dist_sinc (b : NativeBlock) : distPart (fun row => sincM (fx row)) b = [] := by
  unfold distPart
  rw [List.flatMap_append, List.flatMap_append, List.flatMap_map, List.flatMap_map]
  simp only []
  rw [grid_flat _ _ (fun d => sincM (fx d.row)) (fun _ _ => []) (fun i j n1 l1 n2 l2 => cell_sinc _ _ _ _ _ _ _ _ _ _ _ _)]
  simp [hdrD, Desc.row, header_sinc, shardD, shard_sinc]

theorem scan_sinc (b : NativeBlock) (tau : Nat)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    scanPart (fun row => sincM (fx row)) b = b.run.conv.flatMap fun c =>
      ((List.range c.incs.length).filter (fun j => (b.run.used.getD c.cid #[]).getD j false)).map
        (fun j => F (incMsgN b.run c j)) := by
  obtain ⟨-, -, hbase, hD, -, -⟩ := ProcActualRunProjection.run_fields _ tau b.run hr
  unfold scanPart scanDescs
  split
  · rename_i h
    simp only [List.isEmpty_iff] at h
    simp [h]
  · rw [List.flatMap_cons, List.flatMap_assoc]
    simp only []
    have hp : sincM (fx (Desc.param b.run).row) = [] := param_sinc b.run
    rw [hp, List.nil_append]
    apply flatMap_congr_rt
    intro c hcm
    have hf := ProcActualConvertedFacts.run_facts _ _ _ hr c hcm
    have hs := ProcScanConvertedShape.actual _ _ _ hr c hcm
    exact req_sinc_block b.run c _ hbase hD hf.2.2 hs.2.1

theorem filter_flatMap' {α β : Type} (l : List α) (f : α → List β) (p : β → Bool) :
    (l.flatMap f).filter p = l.flatMap (fun a => (f a).filter p) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.filter_append, ih]

theorem filter_lt (len : Nat) (u : Nat → Bool) (h : len ≤ 64) :
    (List.range 64).filter (fun j => decide (j < len) && u j) = (List.range len).filter u := by
  have e : List.range 64 = List.range len ++ List.range' len (64 - len) := by
    have := List.range'_append_1 (s := 0) (m := len) (n := 64 - len)
    rw [Nat.zero_add, show len + (64 - len) = 64 by omega] at this
    rw [List.range_eq_range', List.range_eq_range', this]
  rw [e, List.filter_append]
  have h2 : (List.range' len (64 - len)).filter (fun j => decide (j < len) && u j) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro j hj
    have := (List.mem_range'_1.mp hj).1
    simp; omega
  rw [h2, List.append_nil]
  apply List.filter_congr
  intro j hj
  have := List.mem_range.mp hj
  simp [this]

theorem sinc_reindex (R : Run) (hidx : ∀ k (hk : k < R.conv.length), R.conv[k].cid = k)
    (hlen : ∀ c ∈ R.conv, c.incs.length ≤ 40) :
    R.conv.flatMap (fun c => ((List.range c.incs.length).filter (fun j => (R.used.getD c.cid #[]).getD j false)).map
      (fun j => F (incMsgN R c j))) =
    (SchedRun.usedV R.conv R.used).map (fun v => ProcBus.nf (R.tau :: SchedRun.incOf R.conv v)) := by
  have hconv : R.conv = (List.range R.conv.length).map (fun k => R.conv.getD k default) := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  unfold SchedRun.usedV
  rw [show 64 * R.conv.length = R.conv.length * 64 by omega, ← range_mul, filter_flatMap', List.map_flatMap]
  conv => lhs; rw [hconv, List.flatMap_map]
  apply flatMap_congr_rt
  intro k hk
  have hk' := List.mem_range.mp hk
  have hc : R.conv.getD k default = R.conv[k] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
  have hl := hlen _ (List.getElem_mem hk')
  have hcid := hidx k hk'
  rw [hc, List.filter_map, List.map_map]
  have hf : (List.range 64).filter ((fun v => decide (v % 64 < (R.conv.getD (v / 64) default).incs.length) &&
      SchedRun.usedB R.used (v / 64) (v % 64)) ∘ fun r => k * 64 + r) =
      (List.range 64).filter (fun j => decide (j < R.conv[k].incs.length) && SchedRun.usedB R.used k j) := by
    apply List.filter_congr
    intro j hj
    have hj' := List.mem_range.mp hj
    have h1 : (k * 64 + j) / 64 = k := by omega
    have h2 : (k * 64 + j) % 64 = j := by omega
    simp only [Function.comp_apply, h1, h2, hc]
  rw [hf, filter_lt _ _ (by omega), hcid]
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.mp (List.mem_filter.mp hj).1
  have h1 : (k * 64 + j) / 64 = k := by omega
  have h2 : (k * 64 + j) % 64 = j := by omega
  simp only [Function.comp_apply, F, incMsgN, ProcBus.nf, SchedRun.incOf, h1, h2, hc, hcid, List.map_cons,
    List.map_nil]
  rw [getElem!_pos R.conv[k].incs j hj', show 64 * k + j = k * 64 + j by omega,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]

end ZkFormal.NearV3.Render.SsdBus

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Render.SsdBus ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Candidates NearSpec

theorem covers_sinc_send : Covers Sched.B_SINC true (fun t => t == 12) = true := by decide +kernel
theorem covers_sinc_recv : Covers Sched.B_SINC false (fun t => t == 13) = true := by decide +kernel
theorem pub_sinc (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub Sched.B_SINC s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

/-- **`SINC` balance** of a bundle whose tables 12 and 13 are the scan/distribute and process renders
of the `PriorCore` blocks. -/
theorem balancedAt_sinc {pub : List Fp} (R : RenderBundleV3 pub) {cb : Bytes} {hint : NearSpecV3.Hint}
    {p : NearSpecV3.Prep} (hp : NearSpecV3.prepD0 cb hint = .ok p) {bs : List NativeBlock}
    (hc : PriorCore p NearSpecV3.B0 bs)
    (h12 : (R ⟨12, by decide⟩).tr = ProcScanDistPhases.trace bs)
    (h13 : (R ⟨13, by decide⟩).tr = procTraceV3 (bs.map NativeBlock.run)) :
    R.BalancedAt Sched.B_SINC := by
  intro m
  rw [R.sum_tables true _ m _ covers_sinc_send, R.sum_tables false _ m _ covers_sinc_recv, pub_sinc, pub_sinc]
  have hf1 : (List.range 25).filter (fun t => t == 12) = [12] := by decide
  have hf2 : (List.range 25).filter (fun t => t == 13) = [13] := by decide
  rw [hf1, hf2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [R.cnt_tf 12 (by decide) true, R.cnt_tf 13 (by decide) false, h12, h13]
  have i12 : nearAirV3.tables[12].interactions = ScanDist.table.interactions := rfl
  have i13 : nearAirV3.tables[13].interactions = Proc.tableB.interactions := rfl
  have hcap := (prior_run_capacities hp _ bs hc).2
  rw [i12, i13, ssd_count hp bs hc _ true sincM row_sinc (by simp [sincM, fp_01]) 12 pub m,
    ssd_blocks bs (fun b hb => (hc.valid b hb).2), ProcBus.count_inc _ (by omega)]
  simp only [List.flatMap_map]
  have hd : bs.flatMap (distPart fun row => sincM (fx row)) = [] := by
    simp [dist_sinc]
  rw [hd, List.append_nil]
  have hperm : (bs.flatMap fun b => scanPart (fun row => sincM (fx row)) b).Perm
      (bs.flatMap fun b => ProcBus.incL b.run) := by
    apply Cdc.flatMap_perm'
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    have hr := (hc.indexed i b hi).1.2
    rw [scan_sinc b i hr, sinc_reindex b.run (Ssd.conv_indexed _ _ _ hr)
      (ProcActualConverted.run_converted _ _ _ hr)]
    exact (SchedRun.run_sinc_fp _ _ _ hr).symm
  exact hperm.count_eq m

end RenderBundleV3
end ZkFormal.NearV3.Assembly
