import ZkFormal.NearV3.Render.SchedBusSDLX
import ZkFormal.NearV3.Render.SchedBusRunDecomp

/-!
# `SDG` (bus 58): the distribute grid grants reach the codec

The grid cell of link `l` sends `(τ, l, al, gb, src, has, use)`; the codec record `l` receives
`(τ, l, al, grants[l], srcOf l, has, use)`.  The functional grid's grants array is the spec grid's
(`gridGrants`, row by row: `cells_gridRow`), hence (`link_pass_grid`) the distributed grants of the
block (`GrantWit`); each cell's grant is the final array's entry at its link (`grid_gb`); the cells
(sorted senders × sorted receivers) are a permutation of the links.  **`RenderBundleV3.balancedAt_sdg`**.
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render.Ssd ZkFormal.NearV3.Assembly.CodecDigest
open ProcDistGeneratorFactor ProcDistCellBridge NearSpecV3.Scheduler ProcNativeOldComparisonCapacity

theorem set_self' {α : Type} [Inhabited α] (a : Array α) (i : Nat) : a.set! i a[i]! = a := by
  by_cases hi : i < a.size
  · simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, hi, getElem!_pos a i hi]
  · simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, hi]

section
variable (I : Input) (R : Run)

/-- One row of the functional grid is the spec's `gridRow`. -/
theorem cells_gridRow (i : Nat) : ∀ (js : List Nat) (ds : List Desc) (g : Array (Option Nat))
    (ri : Array (Nat × Nat)) (se : Nat × Nat),
    (js.foldl (cstep I R i) (ds, ProcDistGridAgreement.numerical g, ri, se)).2 =
      let o := gridRow R.n I.allowed (sender I R i) (js.map (receiver I R)) se ri g
      (ProcDistGridAgreement.numerical o.2.2, o.2.1, o.1)
  | [], _, _, _, _ => rfl
  | j :: js, ds, g, ri, se => by
    rw [List.foldl_cons, List.map_cons]
    unfold gridRow
    simp only [cstep]
    have hal : cAl I R i j = I.allowed[sender I R i * R.n + receiver I R j]! := rfl
    by_cases ha : I.allowed[sender I R i * R.n + receiver I R j]! = true
    · rw [hal, ha]
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true, b2n, ProcDistCellRow.grant]
      rw [← ProcDistGridAgreement.numerical_set]
      exact cells_gridRow i js _ _ _ _
    · have ha' : I.allowed[sender I R i * R.n + receiver I R j]! = false := by simpa using ha
      rw [hal, ha']
      simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false, b2n, ProcDistCellRow.grant,
        Nat.sub_zero]
      rw [show ri.set! (receiver I R j) ((ri[receiver I R j]!).1, (ri[receiver I R j]!).2) = ri from set_self' ri _]
      exact cells_gridRow i js _ g ri se

theorem cells_eq_foldl (i : Nat) (st : GS) (m : Nat) : cells I R i st m = (List.range m).foldl (cstep I R i) st := rfl

/-- The spec's grid fold over the first `m` senders. -/
def specFold (m : Nat) : Array Endpoint × Array (Option Nat) :=
  ((List.range m).map (sender I R)).foldl (fun (acc : Array Endpoint × Array (Option Nat)) s =>
      let (_, ri', g') := gridRow R.n I.allowed s ((List.range R.n).map (receiver I R))
        (((List.range R.n).map fun s => (cntS R.n I.allowed s, R.fin.sb[s]!)).toArray[s]!) acc.1 acc.2
      (ri', g'))
    (((List.range R.n).map fun r => (cntR R.n I.allowed r, R.fin.rb[r]!)).toArray, Array.replicate (R.n * R.n) none)

theorem grid_spec : ∀ m, m ≤ R.n →
    (grid I R m).2.1 = ProcDistGridAgreement.numerical (specFold I R m).2 ∧ (grid I R m).2.2.1 = (specFold I R m).1
  | 0, _ => by
    refine ⟨?_, ?_⟩
    · simp [grid, specFold, ProcDistGridAgreement.numerical]
    · simp only [grid, specFold, ri0, List.range_zero, List.map_nil, List.foldl_nil]
      rw [List.map_toArray]
  | m + 1, hm => by
    obtain ⟨h1, h2⟩ := grid_spec m (by omega)
    have hs : ((List.range R.n).map fun s => (cntS R.n I.allowed s, R.fin.sb[s]!)).toArray[sender I R m]! =
        se0 I R m := by
      rw [getElem!_toArray_map_range R.n _ (sender_lt I R m (by omega))]; rfl
    have hrow := cells_gridRow I R m (List.range R.n) [] (specFold I R m).2 (specFold I R m).1 (se0 I R m)
    rw [(grid_succ_eq I R m).2, rowC, h1, h2, cells_eq_foldl, hrow]
    simp only [specFold, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil, hs]
    refine ⟨?_, ?_⟩ <;> first | rfl | trivial

theorem senders_sord : (List.range R.n).map (sender I R) = sordOf R.n I.allowed R.fin.sb := by
  rw [ProcDistGridBridge.sender_list]; rfl

theorem receivers_rord : (List.range R.n).map (receiver I R) = rordOf R.n I.allowed R.fin.rb := by
  rw [ProcDistGridBridge.receiver_list]; rfl

theorem grid_grants : (grid I R R.n).2.1 =
    ProcDistGridAgreement.numerical (gridGrants R.n I.allowed R.fin.sb R.fin.rb
      (sordOf R.n I.allowed R.fin.sb) (rordOf R.n I.allowed R.fin.rb)) := by
  rw [(grid_spec I R R.n (Nat.le_refl _)).1, ← senders_sord, ← receivers_rord]
  rfl

end

/-- The distributed grants of a block are the functional grid's grants. -/
theorem grants_grid (b : NativeBlock) (tau : Nat) (hg : CdcGrant.GrantWit b)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    b.grants = (grid (ProcPreparedSequence.input b.pub b.old) b.run b.run.n).2.1 := by
  obtain ⟨cv, st, rs, ev, sord, rord, hpre, hd⟩ := hg
  obtain ⟨cv', st', rs', ev', s, gs, hpre', -, -, -, -, -, -, -, -, hfin, -⟩ := SchedRun.run_decomp _ tau b.run hr
  rw [hpre] at hpre'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hpre'
  obtain ⟨_, hst, _⟩ := hpre'
  rw [ProcDistGridAgreement.link_pass_grid] at hd
  simp only [Except.ok.injEq, Prod.mk.injEq] at hd
  obtain ⟨_, hnI, _⟩ := ProcActualRunProjection.run_fields _ tau b.run hr
  rw [grid_grants, ← hd.1, hfin, ← hst, hnI]
  rfl

/-- The links of the grid (sorted senders × sorted receivers) are all links. -/
theorem grid_links_perm (I : Input) (R : Run) (g : Nat → List Fp) :
    ((List.range R.n).flatMap fun i => (List.range R.n).map fun j => g (sender I R i * R.n + receiver I R j)).Perm
      ((List.range (R.n * R.n)).map g) := by
  have h1 : ((List.range R.n).flatMap fun i => (List.range R.n).map fun j => g (sender I R i * R.n + receiver I R j)) =
      (ProcDistGridBridge.senders I R).flatMap (fun s => (ProcDistGridBridge.receivers I R).map
        fun r => g (s * R.n + r)) := by
    rw [← ProcDistGridBridge.sender_list, ← ProcDistGridBridge.receiver_list, List.flatMap_map]
    apply flatMap_congr_rt
    intro i _
    rw [List.map_map]
    rfl
  have h2 : ((ProcDistGridBridge.senders I R).flatMap (fun s => (ProcDistGridBridge.receivers I R).map
        fun r => g (s * R.n + r))).Perm ((List.range R.n).flatMap fun s => (List.range R.n).map fun r => g (s * R.n + r)) := by
    refine List.Perm.trans (ZkFormal.NearV3.Render.Cdc.flatMap_perm' _ (fun s _ => ?_))
      ((sortByKey_perm _ _).flatMap_right _)
    exact (sortByKey_perm _ _).map _
  have h3 : ((List.range R.n).flatMap fun s => (List.range R.n).map fun r => g (s * R.n + r)) =
      (List.range (R.n * R.n)).map g := by
    rw [← range_mul R.n R.n, List.map_flatMap]
    apply flatMap_congr_rt
    intro s _
    rw [List.map_map]; rfl
  rw [h1, ← h3]
  exact h2

/-- The `SDG` message of link `l`. -/
def sdgMsg (ids : List Nat) (tv : Nat) (allowed : Array Bool) (gr : Array Nat) (l : Nat) : List Fp :=
  [Fp.ofNat tv, Fp.ofNat l, Fp.ofNat (b2n allowed[l]!), Fp.ofNat gr[l]!,
    Fp.ofNat ((srcFields ids l)[0]! + 256 * (srcFields ids l)[1]!), Fp.ofNat (srcFields ids l)[2]!,
    Fp.ofNat (srcFields ids l)[3]!]

theorem dist_sdg' (I : Input) (R : Run) (gr : Array Nat) (hgr : gr = (grid I R R.n).2.1) :
    (((List.range R.n).map (shardD I R 0)) ++ ((List.range R.n).map (shardD I R 1)) ++
      (grid I R R.n).1).flatMap (fun d => sdgM (fx d.row)) =
    (List.range R.n).flatMap fun i => (List.range R.n).map fun j =>
      sdgMsg I.ids R.tau I.allowed gr (sender I R i * R.n + receiver I R j) := by
  rw [List.flatMap_append, List.flatMap_append, List.flatMap_map, List.flatMap_map, grid_list, List.flatMap_assoc]
  have z : ∀ sd, ((List.range R.n).flatMap fun i => sdgM (fx (shardD I R sd i).row)) = [] := by
    intro sd
    apply List.flatMap_eq_nil_iff.mpr
    intro i _
    exact shard_sdg _ _ _ _ _ _ _ _ _
  rw [z 0, z 1, List.nil_append, List.nil_append]
  apply flatMap_congr_rt
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [List.flatMap_cons, List.flatMap_map]
  have hh : sdgM (fx (hdrD I R i).row) = [] := header_sdg _ _ _ _ _ _
  rw [hh, List.nil_append, ← flat_single']
  apply flatMap_congr_rt
  intro j hj
  have hj' := List.mem_range.mp hj
  have hg := grid_gb I R R.n (Nat.le_refl _) i j hi' hj'
  rw [if_pos hi'] at hg
  have e1 : sdgM (fx (cellAt I R i j (rowC I R i j)).row) =
      [[Fp.ofNat R.tau, Fp.ofNat ((sender I R i * R.n + receiver I R j) % 256 + 256 * ((sender I R i * R.n + receiver I R j) / 256)),
        Fp.ofNat (b2n (cAl I R i j)), Fp.ofNat (gAt I R i j (rowC I R i j)),
        Fp.ofNat ((srcFields I.ids (sender I R i * R.n + receiver I R j))[0]! + 256 * (srcFields I.ids (sender I R i * R.n + receiver I R j))[1]!),
        Fp.ofNat (srcFields I.ids (sender I R i * R.n + receiver I R j))[2]!,
        Fp.ofNat (srcFields I.ids (sender I R i * R.n + receiver I R j))[3]!]] := cell_sdg _ _ _ _ _ _ _ _ _ _ _ _
  rw [e1, ← hg, ← hgr, Nat.mod_add_div]
  rfl

theorem dist_sdg (b : NativeBlock) (tau : Nat) (hg : CdcGrant.GrantWit b)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    distPart (fun row => sdgM (fx row)) b = (List.range b.run.n).flatMap fun i => (List.range b.run.n).map fun j =>
      sdgMsg (ProcPreparedSequence.input b.pub b.old).ids b.run.tau (ProcPreparedSequence.input b.pub b.old).allowed
        b.grants (sender (ProcPreparedSequence.input b.pub b.old) b.run i * b.run.n +
          receiver (ProcPreparedSequence.input b.pub b.old) b.run j) :=
  dist_sdg' _ _ _ (grants_grid b tau hg hr)

theorem codec_sdg (b : NativeBlock) (tau : Nat) (hn64 : b.run.n ≤ 64)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    (Cdc.blkOf b).descs.flatMap Cdc.sdgT = (List.range (b.run.n * b.run.n)).map
      (sdgMsg (ProcPreparedSequence.input b.pub b.old).ids b.run.tau (ProcPreparedSequence.input b.pub b.old).allowed
        b.grants) := by
  obtain ⟨-, hnI, -⟩ := ProcActualRunProjection.run_fields _ tau b.run hr
  rw [Cdc.blk_sdg]
  apply List.map_congr_left
  intro kk _
  simp only [Cdc.blkOf, sdgMsg, srcFields, b2, List.cons_append, List.nil_append, b2n]
  have hsrc : ((srcOf (ProcPreparedSequence.input b.pub b.old).ids kk).getD 0) < 65536 := by
    cases hs : srcOf (ProcPreparedSequence.input b.pub b.old).ids kk with
    | none => simp
    | some k =>
      have := (Cdc.srcOf_spec hs).1
      rw [← hnI] at this
      simp only [Option.getD_some]
      have hn := Nat.mul_le_mul (show b.run.n ≤ 256 by omega) (show b.run.n ≤ 256 by omega)
      omega
  rw [← hnI]
  simp
  refine ⟨rfl, ?_, rfl⟩
  congr 1
  omega

end ZkFormal.NearV3.Render.SsdBus

namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Candidates
open ZkFormal.NearV3.Render.Ssd ZkFormal.NearV3.Assembly.CodecDigest

theorem scan_sdg (b : NativeBlock) : scanPart (fun row => sdgM (fx row)) b = [] := by
  unfold scanPart scanDescs
  split
  · rfl
  · have hp : sdgM (fx (Desc.param b.run).row) = [] := param_sdg b.run
    rw [List.flatMap_cons, List.flatMap_assoc]
    simp only []
    rw [hp, List.nil_append]
    apply List.flatMap_eq_nil_iff.mpr
    intro c _
    apply List.flatMap_eq_nil_iff.mpr
    intro d hd
    obtain ⟨rho, hr, rfl⟩ := List.mem_map.mp hd
    rw [req_row_eq _ _ _ (List.mem_range.mp hr)]
    exact (req_grid b.run c rho _ _).2.2

theorem block_sdg (b : NativeBlock) (tau : Nat) (hn64 : b.run.n ≤ 64) (hg : CdcGrant.GrantWit b)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    (distPart (fun row => sdgM (fx row)) b).Perm ((Cdc.blkOf b).descs.flatMap Cdc.sdgT) := by
  rw [dist_sdg b tau hg hr, codec_sdg b tau hn64 hr]
  exact grid_links_perm _ _ _

end ZkFormal.NearV3.Render.SsdBus

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Render.Cdc ZkFormal.NearV3.Render.SsdBus ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Candidates NearSpec

theorem covers_sdg_send : Covers Sched.B_SDG true (fun t => t == 12) = true := by decide +kernel
theorem covers_sdg_recv : Covers Sched.B_SDG false (fun t => t == 11) = true := by decide +kernel
theorem pub_sdg (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub Sched.B_SDG s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

/-- **`SDG` balance**: the distribute grid grants (12) are what the codec records (11) receive. -/
theorem balancedAt_sdg {cb wb : Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)
    {bs : List NativeBlock} (hc : PriorCore A.p NearSpecV3.B0 bs) (hg : ∀ b ∈ bs, CdcGrant.GrantWit b)
    (h11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 A.pub)
    (h12 : (R ⟨12, by decide⟩).tr = ProcScanDistPhases.trace bs) :
    R.BalancedAt Sched.B_SDG := by
  intro m
  rw [R.sum_tables true _ m _ covers_sdg_send, R.sum_tables false _ m _ covers_sdg_recv, pub_sdg, pub_sdg]
  have hf12 : (List.range 25).filter (fun t => t == 12) = [12] := by decide
  have hf11 : (List.range 25).filter (fun t => t == 11) = [11] := by decide
  rw [hf12, hf11]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [h11, R.cnt_tf 12 (by decide) true, h12]
  have i12 : nearAirV3.tables[12].interactions = ScanDist.table.interactions := rfl
  rw [i12, ssd_count A.hp bs hc _ true sdgM row_sdg (by simp [sdgM, fp_01]) 12 A.pub m,
    ssd_blocks bs (fun b hb => (hc.valid b hb).2),
    codec_sel A.pub _ (prior_cap hc) _ false sdgT (rt_sdg · · 11 A.pub) m]
  have hs : bs.flatMap (scanPart fun row => sdgM (fx row)) = [] :=
    List.flatMap_eq_nil_iff.mpr fun b _ => scan_sdg b
  rw [hs, List.nil_append, List.flatMap_map]
  have hp : (bs.flatMap (distPart fun row => sdgM (fx row))).Perm (bs.flatMap fun b => (blkOf b).descs.flatMap sdgT) := by
    apply flatMap_perm'
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    exact block_sdg b i (hc.valid b hb).2 (hg b hb) (hc.indexed i b hi).1.2
  exact hp.count_eq m

end RenderBundleV3
end ZkFormal.NearV3.Assembly
