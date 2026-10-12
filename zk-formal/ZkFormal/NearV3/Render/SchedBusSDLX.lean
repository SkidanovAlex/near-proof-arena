import ZkFormal.NearV3.Render.SchedBusGridModel

/-!
# `SDLX` (bus 57): the distribute delay line balances

Per run: the sender shard row `i` sends `(τ, i, 255, sᵢ, cntS, sb)`, received by grid header `i`; the
receiver shard row `j` sends `(τ, 0, j, rⱼ, cntR, rb)`, received by cell `(0, j)`; cell `(i, j)` receives
the receiver endpoint before row `i` and (unless `i` is the last row) sends the endpoint after row `i`,
received by cell `(i + 1, j)`.  **`RenderBundleV3.balancedAt_sdlx`**.
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render.Ssd ZkFormal.NearV3.Assembly.CodecDigest
open ProcDistGeneratorFactor ProcDistCellBridge NearSpecV3.Scheduler ProcNativeOldComparisonCapacity

section
variable (I : Input) (R : Run)

/-- Header message of row `i`. -/
def hMsg (i : Nat) : List Fp :=
  F [R.tau, i, 255, sender I R i, cntS R.n I.allowed (sender I R i), R.fin.sb[sender I R i]!]

/-- Pending receiver endpoint of column `j` before row `i`. -/
def pMsg (i j : Nat) : List Fp :=
  F [R.tau, i, j, receiver I R j, ((grid I R i).2.2.1[receiver I R j]!).1, ((grid I R i).2.2.1[receiver I R j]!).2]

theorem sX0 (i : Nat) : sX I R 0 i = sender I R i := rfl
theorem sX1 (j : Nat) : sX I R 1 j = receiver I R j := rfl

theorem shard_parts :
    ((List.range R.n).map (shardD I R 0)).flatMap (fun d => sdlxsM (fx d.row)) = (List.range R.n).map (hMsg I R) ∧
    ((List.range R.n).map (shardD I R 1)).flatMap (fun d => sdlxsM (fx d.row)) =
      (List.range R.n).map (pMsg I R 0) := by
  constructor
  · rw [List.flatMap_map, ← flat_single']
    apply flatMap_congr_rt
    intro i _
    simp only [shardD, Desc.row, shard_sdlxs, ite_true, hMsg, sX0, sC, sL, ProcDistShardRow.nativeCount,
      ProcDistShardRow.nativeLeft]
  · rw [List.flatMap_map, ← flat_single']
    apply flatMap_congr_rt
    intro j hj
    simp only [shardD, Desc.row, shard_sdlxs, show (1 : Nat) ≠ 0 by decide, ite_false, pMsg, sX1, sC, sL,
      ProcDistShardRow.nativeCount, ProcDistShardRow.nativeLeft, grid_ri0 I R j (List.mem_range.mp hj)]

theorem grid_recv : (grid I R R.n).1.flatMap (fun d => sdlxrM (fx d.row)) =
    (List.range R.n).flatMap fun i => hMsg I R i :: (List.range R.n).map (pMsg I R i) := by
  rw [grid_list]
  rw [List.flatMap_assoc]
  apply flatMap_congr_rt
  intro i _
  rw [List.flatMap_cons, List.flatMap_map]
  simp only [hdrD, Desc.row, header_sdlxr]
  rw [← flat_single']
  show _ = [hMsg I R i] ++ _
  refine app_congr rfl ?_
  apply flatMap_congr_rt
  intro j hj
  simp only [cellAt, Desc.row, cell_sdlxr, rowC_ri I R i j (List.mem_range.mp hj)]
  rfl

theorem grid_send (hok : ∀ x ∈ (grid I R R.n).1, CellOk x) : (grid I R R.n).1.flatMap (fun d => sdlxsM (fx d.row)) =
    (List.range R.n).flatMap fun i => if i + 1 = R.n then [] else (List.range R.n).map (pMsg I R (i + 1)) := by
  have hok' := hok
  rw [grid_list] at hok'
  rw [grid_list, List.flatMap_assoc]
  apply flatMap_congr_rt
  intro i hi
  rw [List.flatMap_cons, List.flatMap_map]
  simp only [hdrD, Desc.row, header_sdlxs, List.nil_append]
  by_cases hl : i + 1 = R.n
  · rw [if_pos hl]
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    simp only [cellAt, Desc.row, cell_sdlxs, if_pos hl]
  · rw [if_neg hl, ← flat_single']
    apply flatMap_congr_rt
    intro j hj
    have hj' := List.mem_range.mp hj
    have hc := hok' (cellAt I R i j (rowC I R i j)) (List.mem_flatMap.mpr ⟨i, hi, List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨j, hj, rfl⟩)⟩)
    simp only [cellAt, CellOk] at hc
    simp only [cellAt, Desc.row, cell_sdlxs, if_neg hl, pMsg, F, grid_ri_succ I R i j hj']
    rw [rowC_ri I R i j hj'] at hc ⊢
    rw [fp_sub _ _ (by cases ha : cAl I R i j <;> simp [b2n] <;> simp_all)]
    simp only [gAt, rowC_ri I R i j hj']
    rfl

theorem dist_scan_sdlx (b : NativeBlock) :
    scanPart (fun row => sdlxsM (fx row)) b = [] ∧ scanPart (fun row => sdlxrM (fx row)) b = [] := by
  unfold scanPart scanDescs
  split
  · exact ⟨rfl, rfl⟩
  · have hp1 : sdlxsM (fx (Desc.param b.run).row) = [] := param_sdlxs b.run
    have hp2 : sdlxrM (fx (Desc.param b.run).row) = [] := param_sdlxr b.run
    constructor
    · rw [List.flatMap_cons, List.flatMap_assoc]
      simp only []
      rw [hp1, List.nil_append]
      apply List.flatMap_eq_nil_iff.mpr
      intro c _
      apply List.flatMap_eq_nil_iff.mpr
      intro d hd
      obtain ⟨rho, hr, rfl⟩ := List.mem_map.mp hd
      rw [req_row_eq _ _ _ (List.mem_range.mp hr)]
      exact (req_grid b.run c rho _ _).1
    · rw [List.flatMap_cons, List.flatMap_assoc]
      simp only []
      rw [hp2, List.nil_append]
      apply List.flatMap_eq_nil_iff.mpr
      intro c _
      apply List.flatMap_eq_nil_iff.mpr
      intro d hd
      obtain ⟨rho, hr, rfl⟩ := List.mem_map.mp hd
      rw [req_row_eq _ _ _ (List.mem_range.mp hr)]
      exact (req_grid b.run c rho _ _).2.1

theorem count_cons_flat {α β : Type} [BEq β] (l : List α) (H : α → β) (Q : α → List β) (m : β) :
    (l.flatMap fun i => H i :: Q i).count m = (l.map H).count m + (l.flatMap Q).count m := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.map_cons, List.count_append, List.count_cons] at *; omega

theorem delay_count {β : Type} [BEq β] (n : Nat) (H : Nat → β) (P : Nat → Nat → β) (m : β) :
    ((List.range n).map H ++ (List.range n).map (P 0) ++
      (List.range n).flatMap (fun i => if i + 1 = n then [] else (List.range n).map (P (i + 1)))).count m =
    ((List.range n).flatMap fun i => H i :: (List.range n).map (P i)).count m := by
  rw [count_cons_flat]
  cases n with
  | zero => simp
  | succ k =>
    have h1 : (List.range (k + 1)).flatMap (fun i => if i + 1 = k + 1 then [] else (List.range (k + 1)).map (P (i + 1))) =
        (List.range k).flatMap (fun i => (List.range (k + 1)).map (P (i + 1))) := by
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, ite_true, List.append_nil]
      apply flatMap_congr_rt
      intro i hi
      rw [if_neg (by have := List.mem_range.mp hi; omega)]
    have h2 : (List.range (k + 1)).flatMap (fun i => (List.range (k + 1)).map (P i)) =
        (List.range (k + 1)).map (P 0) ++ (List.range k).flatMap (fun i => (List.range (k + 1)).map (P (i + 1))) := by
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    rw [h1, h2]
    simp only [List.count_append]
    omega

/-- **`SDLX` per run.** -/
theorem block_sdlx (b : NativeBlock) (hn : b.run.n ≤ 64) (m : List Fp) :
    (distPart (fun row => sdlxsM (fx row)) b).count m = (distPart (fun row => sdlxrM (fx row)) b).count m := by
  have hok := dist_ok _ _ _ (distribution_eq b hn)
  unfold distPart
  simp only [List.flatMap_append]
  obtain ⟨h0, h1⟩ := shard_parts (ProcPreparedSequence.input b.pub b.old) b.run
  rw [h0, h1, grid_send _ _ hok, grid_recv]
  have z0 : ((List.range b.run.n).map (shardD (ProcPreparedSequence.input b.pub b.old) b.run 0)).flatMap
      (fun d => sdlxrM (fx d.row)) = [] := by
    simp [List.flatMap_map, shardD, Desc.row, shard_sdlxr]
  have z1 : ((List.range b.run.n).map (shardD (ProcPreparedSequence.input b.pub b.old) b.run 1)).flatMap
      (fun d => sdlxrM (fx d.row)) = [] := by
    simp [List.flatMap_map, shardD, Desc.row, shard_sdlxr]
  rw [z0, z1, List.nil_append, List.nil_append]
  exact delay_count _ _ _ m

end

end ZkFormal.NearV3.Render.SsdBus

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Render.SsdBus ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Candidates NearSpec

theorem covers_sdlx (s : Bool) : Covers Sched.B_SDLX s (fun t => t == 12) = true := by cases s <;> decide +kernel
theorem pub_sdlx (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub Sched.B_SDLX s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

/-- **`SDLX` balance**: the scan/distribute table (12) of the `PriorCore` blocks balances its delay line. -/
theorem balancedAt_sdlx {cb wb : Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)
    {bs : List NativeBlock} (hc : PriorCore A.p NearSpecV3.B0 bs)
    (h12 : (R ⟨12, by decide⟩).tr = ProcScanDistPhases.trace bs) :
    R.BalancedAt Sched.B_SDLX := by
  intro m
  rw [R.sum_tables true _ m _ (covers_sdlx true), R.sum_tables false _ m _ (covers_sdlx false), pub_sdlx, pub_sdlx]
  have hf : (List.range 25).filter (fun t => t == 12) = [12] := by decide
  rw [hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [R.cnt_tf 12 (by decide) true, R.cnt_tf 12 (by decide) false, h12]
  have i12 : nearAirV3.tables[12].interactions = ScanDist.table.interactions := rfl
  rw [i12, ssd_count A.hp bs hc _ true sdlxsM row_sdlxs (by simp [sdlxsM, fp_01]) 12 A.pub m,
    ssd_count A.hp bs hc _ false sdlxrM row_sdlxr (by simp [sdlxrM, fp_01]) 12 A.pub m,
    ssd_blocks bs (fun b hb => (hc.valid b hb).2), ssd_blocks bs (fun b hb => (hc.valid b hb).2)]
  have hs1 : bs.flatMap (scanPart fun row => sdlxsM (fx row)) = [] :=
    List.flatMap_eq_nil_iff.mpr fun b _ => (dist_scan_sdlx b).1
  have hs2 : bs.flatMap (scanPart fun row => sdlxrM (fx row)) = [] :=
    List.flatMap_eq_nil_iff.mpr fun b _ => (dist_scan_sdlx b).2
  rw [hs1, hs2, List.nil_append, List.nil_append]
  have key : ∀ cs : List NativeBlock, (∀ b ∈ cs, b ∈ bs) →
      (cs.flatMap (distPart fun row => sdlxsM (fx row))).count m =
        (cs.flatMap (distPart fun row => sdlxrM (fx row))).count m := by
    intro cs hcs
    induction cs with
    | nil => rfl
    | cons b cs ih =>
      simp only [List.flatMap_cons, List.count_append]
      rw [block_sdlx b (hc.valid b (hcs b (by simp))).2 m, ih (fun x hx => hcs x (by simp [hx]))]
  exact key bs (fun _ h => h)

end RenderBundleV3
end ZkFormal.NearV3.Assembly
