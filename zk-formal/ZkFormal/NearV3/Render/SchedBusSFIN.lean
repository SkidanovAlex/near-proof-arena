import ZkFormal.NearV3.Render.SchedBusSINC

/-!
# `SFIN` (bus 42): final memory values balance

The memory (14) sends `(addr, vfin, wfin)` per segment; the codec (11) receives the links'
`(addr, afin, gfin)` (the run's final link values, by construction of `blkOf`) and the distribute
shard rows (12) receive the budgets `(addr, left, 0)` (in sorted order: a permutation).
**`RenderBundleV3.balancedAt_sfin`**.
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render.Ssd ZkFormal.NearV3.Assembly.CodecDigest
open NearSpecV3.Scheduler

theorem dist_sfin (b : NativeBlock) :
    distPart (fun row => sfinM (fx row)) b =
      (List.range b.run.n).map (fun i => F (finMsg (ProcPreparedSequence.input b.pub b.old) b.run 0 i)) ++
      (List.range b.run.n).map (fun i => F (finMsg (ProcPreparedSequence.input b.pub b.old) b.run 1 i)) :=
  (dist_ops (ProcPreparedSequence.input b.pub b.old) b.run).2.1

theorem fin_side (I : Input) (R : Run) (sd : Nat) (hsd : sd = 0 ∨ sd = 1) :
    ((List.range R.n).map (fun i => F (finMsg I R sd i))).Perm
      ((List.range R.n).map (fun x => ProcBus.nf [addrOf R.tau (sd + 1) x,
        if sd = 0 then R.fin.sb[x]! else R.fin.rb[x]!, 0])) := by
  let key := fun x => if sd = 0 then ProcDistShardRow.average (cntS R.n I.allowed x) R.fin.sb[x]!
    else ProcDistShardRow.average (cntR R.n I.allowed x) R.fin.rb[x]!
  refine List.Perm.trans (List.Perm.of_eq ?_) (sorted_map key R.n _)
  apply List.map_congr_left
  intro i _
  rcases hsd with rfl | rfl
  · simp only [F, finMsg, ProcBus.nf, sX, sL, ProcDistShardRow.nativeX, ProcDistShardRow.nativeLeft, key,
      ite_true, addrOf]
    congr 2; omega
  · simp only [F, finMsg, ProcBus.nf, sX, sL, ProcDistShardRow.nativeX, ProcDistShardRow.nativeLeft, key,
      ite_false, addrOf, show (1 : Nat) ≠ 0 by decide]
    congr 2; omega

theorem fin_side0 (I : Input) (R : Run) :
    ((List.range R.n).map (fun i => F (finMsg I R 0 i))).Perm
      ((List.range R.n).map (ProcBus.nf ∘ fun x => [addrOf R.tau 1 x, R.fin.sb[x]!, 0])) := by
  have := fin_side I R 0 (Or.inl rfl)
  simpa [Function.comp_def] using this

theorem fin_side1 (I : Input) (R : Run) :
    ((List.range R.n).map (fun i => F (finMsg I R 1 i))).Perm
      ((List.range R.n).map (ProcBus.nf ∘ fun x => [addrOf R.tau 2 x, R.fin.rb[x]!, 0])) := by
  have := fin_side I R 1 (Or.inr rfl)
  simpa [Function.comp_def] using this

theorem codec_sfin (b : NativeBlock) :
    (Cdc.blkOf b).descs.flatMap Cdc.sfinT =
      (List.range (b.run.n * b.run.n)).map (fun l =>
        ProcBus.nf [addrOf b.run.tau 0 l, (b.run.segs.getD l default).vfin, (b.run.segs.getD l default).wfin]) := by
  rw [Cdc.blk_sfin]
  apply List.map_congr_left
  intro l _
  simp only [Cdc.blkOf, ProcBus.nf, addrOf, List.map_cons, List.map_nil]
  congr 2; omega

end ZkFormal.NearV3.Render.SsdBus

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Render.SsdBus ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Candidates NearSpec

theorem covers_sfin_send : Covers Sched.B_SFIN true (fun t => t == 14) = true := by decide +kernel
theorem covers_sfin_recv : Covers Sched.B_SFIN false (fun t => t == 11 || t == 12) = true := by decide +kernel
theorem pub_sfin (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub Sched.B_SFIN s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

/-- **`SFIN` balance**: tables 11, 12, 14 of the `PriorCore` blocks. -/
theorem balancedAt_sfin {pub : List Fp} (R : RenderBundleV3 pub) {cb : Bytes} {hint : NearSpecV3.Hint}
    {p : NearSpecV3.Prep} (hp : NearSpecV3.prepD0 cb hint = .ok p) {bs : List NativeBlock}
    (hc : PriorCore p NearSpecV3.B0 bs)
    (h11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (Cdc.codecCell (bs.map Cdc.blkOf)) 22 11 pub)
    (h12 : (R ⟨12, by decide⟩).tr = ProcScanDistPhases.trace bs)
    (h14 : (R ⟨14, by decide⟩).tr = MemConcatCells.trace (bs.map NativeBlock.run)) :
    R.BalancedAt Sched.B_SFIN := by
  intro m
  rw [R.sum_tables true _ m _ covers_sfin_send, R.sum_tables false _ m _ covers_sfin_recv, pub_sfin, pub_sfin]
  have hf1 : (List.range 25).filter (fun t => t == 14) = [14] := by decide
  have hf2 : (List.range 25).filter (fun t => t == 11 || t == 12) = [11, 12] := by decide
  rw [hf1, hf2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [R.cnt_tf 14 (by decide) true, R.cnt_tf 12 (by decide) false, h12, h14, h11]
  have i12 : nearAirV3.tables[12].interactions = ScanDist.table.interactions := rfl
  have i14 : nearAirV3.tables[14].interactions = Mem.interactions := rfl
  have hcap := (prior_run_capacities hp _ bs hc).1
  have e1 := codec_sel pub _ (Cdc.prior_cap hc) _ false Cdc.sfinT (Cdc.rt_sfin · · 11 pub) m
  rw [i12, i14, e1, ssd_count hp bs hc _ false sfinM row_sfin (by simp [sfinM, fp_01]) 12 pub m,
    ssd_blocks bs (fun b hb => (hc.valid b hb).2), MemBus.count_fin _ hcap]
  simp only [List.flatMap_map]
  have hs : bs.flatMap (scanPart fun row => sfinM (fx row)) = [] := by simp [scan_sfin]
  rw [hs, List.nil_append]
  have hperm : (bs.flatMap fun b => (Cdc.blkOf b).descs.flatMap Cdc.sfinT ++ distPart (fun row => sfinM (fx row)) b).Perm
      (MemBus.finML (bs.map NativeBlock.run)) := by
    unfold MemBus.finML
    rw [List.flatMap_map]
    apply Cdc.flatMap_perm'
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    have hr := (hc.indexed i b hi).1.2
    obtain ⟨ht, hnI, -⟩ := ProcActualRunProjection.run_fields _ i b.run hr
    rw [codec_sfin b, dist_sfin, SchedRun.run_sfin _ _ _ hr, ← hnI, ← ht]
    simp only [List.map_append, List.map_map]
    have p0 := fin_side0 (ProcPreparedSequence.input b.pub b.old) b.run
    have p1 := fin_side1 (ProcPreparedSequence.input b.pub b.old) b.run
    rw [List.perm_iff_count]
    intro a
    have c0 := p0.count_eq a
    have c1 := p1.count_eq a
    simp only [List.count_append, List.map_map] at c0 c1 ⊢
    have e : (List.range (b.run.n * b.run.n)).map (fun l => ProcBus.nf [addrOf b.run.tau 0 l,
        (b.run.segs.getD l default).vfin, (b.run.segs.getD l default).wfin]) =
      (List.range (b.run.n * b.run.n)).map (ProcBus.nf ∘ fun l => [addrOf b.run.tau 0 l,
        (b.run.segs.getD l default).vfin, (b.run.segs.getD l default).wfin]) := rfl
    rw [e]
    omega
  have h := hperm.count_eq m
  rw [count_flatMap_app2] at h
  omega

end RenderBundleV3
end ZkFormal.NearV3.Assembly
