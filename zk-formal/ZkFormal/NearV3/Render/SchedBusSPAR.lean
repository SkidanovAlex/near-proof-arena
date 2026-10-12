import ZkFormal.NearV3.Render.SchedBusConv
import ZkFormal.NearV3.Render.SchedBusPub

/-!
# `SPAR` (bus 52): the public scheduler parameters balance

The public statement sends, per instance, the codec header record (tag 0), the scan parameters
(tag 1, instances with requests), one raw request record per converted request (tag 2), one shard
record per shard and side (tag 3) and one link record per link (tag 4).  The codec header row receives
tag 0; the scan param row tag 1; the first row of every request tag 2; the distribute shard rows tag 3
(in sorted order: a permutation) and the grid cells tag 4 (sorted senders × sorted receivers: a
permutation of the links).  **`RenderBundleV3.balancedAt_spar`**.
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render.Ssd ZkFormal.NearV3.Assembly.CodecDigest
open ProcNativeOldComparisonCapacity ProcDistCellBridge NearSpecV3.Scheduler
open ZkFormal.NearV3.Assembly (recF)

def F (l : List Nat) : List Fp := l.map Fp.ofNat

def paramMsg (R : Run) : List Nat :=
  [R.tau, 1, Scan.byteOf R.base 0, Scan.byteOf R.base 1, Scan.byteOf R.base 2, Scan.byteOf R.D 0,
    Scan.byteOf R.D 1, Scan.byteOf R.D 2, R.n, 0, 0]

def rawMsg (R : Run) (c : CReq) : List Nat :=
  [R.tau, 2, (c.bm.map (·.toNat)).getD 0 0, (c.bm.map (·.toNat)).getD 1 0, (c.bm.map (·.toNat)).getD 2 0,
    (c.bm.map (·.toNat)).getD 3 0, (c.bm.map (·.toNat)).getD 4 0, c.cid % 256, c.cid / 256, c.s, c.r]

theorem range20_flat (g : Nat → List (List Fp)) (h : ∀ rho, 0 < rho → rho < 20 → g rho = []) :
    (List.range 20).flatMap g = g 0 := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  simp only [h 1 (by decide) (by decide), h 2 (by decide) (by decide), h 3 (by decide) (by decide),
    h 4 (by decide) (by decide), h 5 (by decide) (by decide), h 6 (by decide) (by decide), h 7 (by decide) (by decide),
    h 8 (by decide) (by decide), h 9 (by decide) (by decide), h 10 (by decide) (by decide),
    h 11 (by decide) (by decide), h 12 (by decide) (by decide), h 13 (by decide) (by decide),
    h 14 (by decide) (by decide), h 15 (by decide) (by decide), h 16 (by decide) (by decide),
    h 17 (by decide) (by decide), h 18 (by decide) (by decide), h 19 (by decide) (by decide), List.append_nil]

theorem req_row_eq (R : Run) (c : CReq) (rho : Nat) (h : rho < 20) :
    (Desc.req R c rho).row = ProcScanRequestFactor.row R c rho (ProcScanRequestCount.before c.bm rho)
      (ProcScanRequestState.state R c rho).2.2 :=
  ProcScanRequestState.native_at R c rho h

theorem flat_single' {α β : Type} (l : List α) (f : α → β) : l.flatMap (fun a => [f a]) = l.map f := by
  induction l <;> simp_all

theorem req_block_spar (R : Run) (c : CReq) :
    ((List.range 20).map (Desc.req R c)).flatMap (fun d => sparM (fx d.row)) = [F (rawMsg R c)] := by
  rw [List.flatMap_map]
  have h1 : ∀ rho ∈ List.range 20, sparM (fx (Desc.req R c rho).row) =
      if rho = 0 then [F (rawMsg R c)] else [] := by
    intro rho hr
    rw [req_row_eq _ _ _ (List.mem_range.mp hr), req_spar]; rfl
  rw [flatMap_congr_rt h1]
  simp [List.range_succ]

theorem scan_spar (b : NativeBlock) :
    scanPart (fun row => sparM (fx row)) b =
      if b.run.conv.isEmpty then [] else F (paramMsg b.run) :: b.run.conv.map (fun c => F (rawMsg b.run c)) := by
  unfold scanPart scanDescs
  split
  · rfl
  · rw [List.flatMap_cons, List.flatMap_assoc]
    simp only []
    have hp : sparM (fx (Desc.param b.run).row) = [F (paramMsg b.run)] := param_spar b.run
    rw [hp, flatMap_congr_rt (fun c _ => req_block_spar b.run c), flat_single']
    rfl

def shardMsg (I : Input) (R : Run) (sd i : Nat) : List Nat :=
  [R.tau, 3, sd, sX I R sd i, sC I R sd i, sB I R sd i % 256, sB I R sd i / 256 % 256, sB I R sd i / 65536 % 256,
    R.n, 0, 0]

def linkMsg (ids : List Nat) (tv l : Nat) (al : Bool) : List Nat :=
  [tv, 4, (srcFields ids l)[0]!, (srcFields ids l)[1]!, (srcFields ids l)[2]!, (srcFields ids l)[3]!, 0, 0,
    l % 256, l / 256, b2n al]

theorem dist_spar' (I : Input) (R : Run) :
    (((List.range R.n).map (shardD I R 0)) ++ ((List.range R.n).map (shardD I R 1)) ++
      (grid I R R.n).1).flatMap (fun d => sparM (fx d.row)) =
      (List.range R.n).map (fun i => F (shardMsg I R 0 i)) ++
      (List.range R.n).map (fun i => F (shardMsg I R 1 i)) ++
      (List.range R.n).flatMap (fun i => (List.range R.n).map fun j =>
        F (linkMsg I.ids R.tau (sender I R i * R.n + receiver I R j) (cAl I R i j))) := by
  rw [List.flatMap_append, List.flatMap_append, List.flatMap_map, List.flatMap_map]
  rw [grid_flat I R (fun d => sparM (fx d.row))
    (fun i j => [F (linkMsg I.ids R.tau (sender I R i * R.n + receiver I R j) (cAl I R i j))])
    (fun i j n1 l1 n2 l2 => cell_spar _ _ _ _ _ _ _ _ _ _ _ _)]
  simp only [hdrD, Desc.row, header_spar, List.nil_append, shardD, shard_spar, ← flat_single']
  rfl

theorem dist_spar (b : NativeBlock) :
    distPart (fun row => sparM (fx row)) b =
      (List.range b.run.n).map (fun i => F (shardMsg (ProcPreparedSequence.input b.pub b.old) b.run 0 i)) ++
      (List.range b.run.n).map (fun i => F (shardMsg (ProcPreparedSequence.input b.pub b.old) b.run 1 i)) ++
      (List.range b.run.n).flatMap (fun i => (List.range b.run.n).map fun j =>
        F (linkMsg (ProcPreparedSequence.input b.pub b.old).ids b.run.tau
          (sender (ProcPreparedSequence.input b.pub b.old) b.run i * b.run.n +
            receiver (ProcPreparedSequence.input b.pub b.old) b.run j)
          (cAl (ProcPreparedSequence.input b.pub b.old) b.run i j))) :=
  dist_spar' _ _

/-! ## Native identities -/

theorem sorted_map (key : Nat → Nat) (n : Nat) (g : Nat → List Fp) :
    ((List.range n).map fun i => g ((sortByKey key (List.range n))[i]!)).Perm ((List.range n).map g) := by
  have hl : (sortByKey key (List.range n)).length = n := (sortByKey_perm _ _).length_eq.trans List.length_range
  have h1 : (List.range n).map (fun i => g ((sortByKey key (List.range n))[i]!)) =
      (sortByKey key (List.range n)).map g := by
    conv => rhs; rw [← ProcDistGridBridge.indexed_list (sortByKey key (List.range n)), hl, List.map_map]
    rfl
  rw [h1]
  exact (sortByKey_perm key _).map g

theorem range_mul (a b : Nat) : (List.range a).flatMap (fun s => (List.range b).map (fun r => s * b + r)) =
    List.range (a * b) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add]
    simp [List.range_eq_range']

/-- The public `SPAR` records of one instance (as `Sched.render` emits them). -/
def pubBlock (τ : Nat) (P : InstPub) : List (List Nat) :=
  [parCodec τ P] ++ (if P.raw.isEmpty then [] else [parScan τ P]) ++ rawRecs τ P ++ shardRecs τ P ++ linkRecs τ P

theorem getD_toNat (l : List UInt8) (i : Nat) : (l.map (·.toNat)).getD i 0 = (l.getD i 0).toNat := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem instOf_filter (sp : SchedPub) :
    (instOf sp).raw.filter (fun q => !(setBits q.bm).isEmpty) = (instOf sp).raw := by
  apply List.filter_eq_self.mpr
  intro q hq
  simp only [instOf, List.mem_filter] at hq
  have h2 := hq.2
  cases hb : setBits q.bm with
  | nil => simp [incsOf, hb, incsFrom] at h2
  | cons _ _ => simp

theorem conv_raw (b : NativeBlock) (tau : Nat)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    b.run.conv.map cv3 = (instOf b.pub).raw.map qv3 := by
  rw [run_conv3 _ _ _ hr]
  exact congrArg (List.map qv3) (instOf_filter b.pub)

theorem raw_recs (b : NativeBlock) (tau : Nat)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) (hL : b.run.conv.length < 65536) :
    b.run.conv.map (fun c => F (rawMsg b.run c)) = recF (rawRecs b.run.tau (instOf b.pub)) := by
  have h3 := conv_raw b tau hr
  have hlen : b.run.conv.length = (instOf b.pub).raw.length := by
    have := congrArg List.length h3; simpa using this
  have hidx := conv_indexed _ _ _ hr
  apply List.ext_getElem
  · simp [recF, rawRecs, hlen]
  · intro k h1 h2
    simp only [List.length_map] at h1
    have hk := congrArg (fun l => l[k]?) h3
    simp only [List.getElem?_map, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem (show k < (instOf b.pub).raw.length by omega), Option.map_some,
      Option.some.injEq, cv3, qv3, Prod.mk.injEq] at hk
    obtain ⟨hbm, hs, hrr⟩ := hk
    simp only [List.getElem_map, recF, rawRecs, List.getElem_zip, List.getElem_range, F, rawMsg, hidx k h1,
      getD_toNat, hbm, hs, hrr, b2, PT_RAW, List.range_succ, List.range_zero]
    simp
    rw [Nat.mod_eq_of_lt (by omega : k / 256 < 256)]

theorem param_msg (b : NativeBlock) (tau : Nat)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    F (paramMsg b.run) = F (parScan b.run.tau (instOf b.pub)) := by
  obtain ⟨-, hnI, hbase, hD, -, -⟩ := ProcActualRunProjection.run_fields _ tau b.run hr
  simp only [F, paramMsg, parScan, b3, Scan.byteOf, hnI, hbase, hD, PT_SCAN, InstPub.n, instOf,
    ProcPreparedSequence.input, List.cons_append, List.nil_append, List.map_cons, List.map_nil]
  simp

def shardRec (P : InstPub) (τ sd x : Nat) : List Nat :=
  [τ, PT_SHD, sd, x, if sd = 0 then cntS P.n P.allowed x else cntR P.n P.allowed x] ++ b3 (budget0 P sd x) ++
    [P.n, 0, 0]

theorem shard_side (b : NativeBlock) (tau : Nat) (sd : Nat) (hsd : sd = 0 ∨ sd = 1)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    ((List.range b.run.n).map (fun i => F (shardMsg (ProcPreparedSequence.input b.pub b.old) b.run sd i))).Perm
      ((List.range b.run.n).map (fun x => F (shardRec (instOf b.pub) b.run.tau sd x))) := by
  obtain ⟨-, hnI, -, -, -, -⟩ := ProcActualRunProjection.run_fields _ tau b.run hr
  have hn : (instOf b.pub).n = b.run.n := by rw [hnI]; rfl
  let I := ProcPreparedSequence.input b.pub b.old
  let key := fun x => if sd = 0 then ProcDistShardRow.average (cntS b.run.n I.allowed x) b.run.fin.sb[x]!
    else ProcDistShardRow.average (cntR b.run.n I.allowed x) b.run.fin.rb[x]!
  refine List.Perm.trans (List.Perm.of_eq ?_) (sorted_map key b.run.n _)
  apply List.map_congr_left
  intro i _
  rcases hsd with rfl | rfl
  · simp only [F, shardMsg, shardRec, sX, sC, sB, ProcDistShardRow.nativeX, ProcDistShardRow.nativeCount, hn, key,
      ite_true, b3, PT_SHD, List.cons_append, List.nil_append]
    rfl
  · simp only [F, shardMsg, shardRec, sX, sC, sB, ProcDistShardRow.nativeX, ProcDistShardRow.nativeCount, hn, key,
      ite_false, b3, PT_SHD, List.cons_append, List.nil_append, show (1 : Nat) ≠ 0 by decide]
    rfl

theorem shard_perm (b : NativeBlock) (tau : Nat)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    ((List.range b.run.n).map (fun i => F (shardMsg (ProcPreparedSequence.input b.pub b.old) b.run 0 i)) ++
      (List.range b.run.n).map (fun i => F (shardMsg (ProcPreparedSequence.input b.pub b.old) b.run 1 i))).Perm
      (recF (shardRecs b.run.tau (instOf b.pub))) := by
  obtain ⟨-, hnI, -, -, -, -⟩ := ProcActualRunProjection.run_fields _ tau b.run hr
  have hn : (instOf b.pub).n = b.run.n := by rw [hnI]; rfl
  have hR : recF (shardRecs b.run.tau (instOf b.pub)) =
      (List.range b.run.n).map (fun x => F (shardRec (instOf b.pub) b.run.tau 0 x)) ++
      (List.range b.run.n).map (fun x => F (shardRec (instOf b.pub) b.run.tau 1 x)) := by
    simp [shardRecs, recF, F, shardRec, hn, Function.comp_def]
  rw [hR]
  exact (shard_side b tau 0 (Or.inl rfl) hr).append (shard_side b tau 1 (Or.inr rfl) hr)

theorem linkMsg_eq (P : InstPub) (τ l : Nat) (hl : l < 65536) :
    F (linkMsg P.ids τ l P.allowed[l]!) =
      F ([τ, PT_LINK] ++ srcFields P.ids l ++ [0, 0] ++ b2 l ++ [P.al l]) := by
  simp only [F, linkMsg, srcFields, b2, PT_LINK, InstPub.al, b2n, List.cons_append, List.nil_append,
    List.append_assoc, List.map_cons, List.map_nil, List.map_append]
  simp
  rw [Nat.mod_eq_of_lt (by omega : l / 256 < 256)]

theorem link_perm (b : NativeBlock) (tau : Nat) (hn64 : b.run.n ≤ 64)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    ((List.range b.run.n).flatMap (fun i => (List.range b.run.n).map fun j =>
        F (linkMsg (ProcPreparedSequence.input b.pub b.old).ids b.run.tau
          (sender (ProcPreparedSequence.input b.pub b.old) b.run i * b.run.n +
            receiver (ProcPreparedSequence.input b.pub b.old) b.run j)
          (cAl (ProcPreparedSequence.input b.pub b.old) b.run i j)))).Perm
      (recF (linkRecs b.run.tau (instOf b.pub))) := by
  obtain ⟨-, hnI, -, -, -, -⟩ := ProcActualRunProjection.run_fields _ tau b.run hr
  have hn : (instOf b.pub).n = b.run.n := by rw [hnI]; rfl
  let I := ProcPreparedSequence.input b.pub b.old
  let n := b.run.n
  let g : Nat → List Fp := fun l => F (linkMsg I.ids b.run.tau l I.allowed[l]!)
  have h1 : (List.range n).flatMap (fun i => (List.range n).map fun j =>
        F (linkMsg I.ids b.run.tau (sender I b.run i * n + receiver I b.run j) (cAl I b.run i j))) =
      (ProcDistGridBridge.senders I b.run).flatMap (fun s => (ProcDistGridBridge.receivers I b.run).map
        fun r => g (s * n + r)) := by
    rw [← ProcDistGridBridge.sender_list, ← ProcDistGridBridge.receiver_list, List.flatMap_map]
    apply flatMap_congr_rt
    intro i _
    rw [List.map_map]
    rfl
  have h2 : ((ProcDistGridBridge.senders I b.run).flatMap (fun s => (ProcDistGridBridge.receivers I b.run).map
        fun r => g (s * n + r))).Perm ((List.range n).flatMap fun s => (List.range n).map fun r => g (s * n + r)) := by
    refine List.Perm.trans (ZkFormal.NearV3.Render.Cdc.flatMap_perm' _ (fun s _ => ?_))
      ((sortByKey_perm _ _).flatMap_right _)
    exact (sortByKey_perm _ _).map _
  have h3 : ((List.range n).flatMap fun s => (List.range n).map fun r => g (s * n + r)) =
      (List.range (n * n)).map g := by
    rw [← range_mul n n, List.map_flatMap]
    apply flatMap_congr_rt
    intro s _
    rw [List.map_map]; rfl
  have h4 : recF (linkRecs b.run.tau (instOf b.pub)) = (List.range (n * n)).map g := by
    unfold linkRecs recF
    rw [hn, List.map_map]
    apply List.map_congr_left
    intro l hl
    have hl' := List.mem_range.mp hl
    have : b.run.n * b.run.n ≤ 4096 := by have := Nat.mul_le_mul hn64 hn64; omega
    exact (linkMsg_eq (instOf b.pub) b.run.tau l (by omega)).symm
  show ((List.range n).flatMap (fun i => (List.range n).map fun j =>
        F (linkMsg I.ids b.run.tau (sender I b.run i * n + receiver I b.run j) (cAl I b.run i j)))).Perm _
  rw [h1, h4, ← h3]
  exact h2

theorem codec_spar (b : NativeBlock) (tau : Nat)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    (Cdc.blkOf b).descs.flatMap Cdc.sparT = [F (parCodec b.run.tau (instOf b.pub))] := by
  obtain ⟨-, hnI, -, -, -, -⟩ := ProcActualRunProjection.run_fields _ tau b.run hr
  have hn : (instOf b.pub).n = b.run.n := by rw [hnI]; rfl
  rw [Cdc.blk_spar]
  simp only [F, parCodec, hn, b2, b3, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    Cdc.blkOf]
  rfl

/-- **`SPAR` per block**: codec, scan and distribute receives are the instance's public records. -/
theorem block_spar (b : NativeBlock) (tau : Nat) (hn64 : b.run.n ≤ 64) (hraw : (instOf b.pub).raw.length ≤ 4096)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    ((Cdc.blkOf b).descs.flatMap Cdc.sparT ++ scanPart (fun row => sparM (fx row)) b ++
      distPart (fun row => sparM (fx row)) b).Perm (recF (pubBlock b.run.tau (instOf b.pub))) := by
  have h3 := conv_raw b tau hr
  have hlen : b.run.conv.length = (instOf b.pub).raw.length := by
    have := congrArg List.length h3; simpa using this
  have e2 : (if b.run.conv.isEmpty then [] else F (paramMsg b.run) :: b.run.conv.map (fun c => F (rawMsg b.run c))) =
      recF (if (instOf b.pub).raw.isEmpty then [] else [parScan b.run.tau (instOf b.pub)]) ++
        recF (rawRecs b.run.tau (instOf b.pub)) := by
    by_cases he : (instOf b.pub).raw = []
    · have hc : b.run.conv = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, he]; rfl)
      simp [hc, he, rawRecs, recF]
    · have hc : b.run.conv ≠ [] := fun h => he (List.eq_nil_of_length_eq_zero (by rw [← hlen, h]; rfl))
      simp only [List.isEmpty_iff, hc, he, ite_false]
      rw [param_msg b tau hr, raw_recs b tau hr (by omega)]
      rfl
  have p3 := shard_perm b tau hr
  have p4 := link_perm b tau hn64 hr
  rw [codec_spar b tau hr, scan_spar, dist_spar, e2]
  unfold pubBlock
  rw [List.perm_iff_count]
  intro a
  have c3 := p3.count_eq a
  have c4 := p4.count_eq a
  simp only [recF, List.map_append, List.count_append, List.map_cons, List.map_nil, F] at c3 c4 ⊢
  omega

end ZkFormal.NearV3.Render.SsdBus

namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Assembly.CodecDigest

theorem flatMap_instAt {α : Type} (X : Nat → InstPub → List α) (f : NativeBlock → InstPub) :
    ∀ (bs : List NativeBlock) (pre : List InstPub), (∀ i b, bs[i]? = some b → b.run.tau = pre.length + i) →
    (List.range' pre.length bs.length).flatMap (fun τ => X τ (Assembly.instAt (pre ++ bs.map f) τ)) =
      bs.flatMap (fun b => X b.run.tau (f b))
  | [], _, _ => rfl
  | b :: bs, pre, ht => by
    have h0 : b.run.tau = pre.length := by simpa using ht 0 b rfl
    have ih := flatMap_instAt X f bs (pre ++ [f b]) (fun i x hx => by
      have := ht (i + 1) x (by simpa using hx); simp; omega)
    simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      List.map_cons] at ih
    rw [List.length_cons, List.range'_succ, List.flatMap_cons, List.flatMap_cons]
    simp only [List.map_cons]
    rw [ih, h0]
    congr 2
    simp [Assembly.instAt, List.getD_eq_getElem?_getD]

theorem count_flatMap_app3 {α β : Type} [BEq β] (l : List α) (f g h : α → List β) (m : β) :
    (l.flatMap (fun a => f a ++ g a ++ h a)).count m =
      (l.flatMap f).count m + (l.flatMap g).count m + (l.flatMap h).count m := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.count_append] at *; omega

end ZkFormal.NearV3.Render.SsdBus

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Render.Cdc ZkFormal.NearV3.Render.SsdBus ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Candidates NearSpec

theorem covers_spar_send : Covers Sched.B_SPAR true (fun _ => false) = true := by decide +kernel
theorem covers_spar_recv : Covers Sched.B_SPAR false (fun t => t == 11 || t == 12) = true := by decide +kernel
theorem pub_spar_recv (pub m : List Fp) : pubCount nearAirV3 pub Sched.B_SPAR false m = 0 :=
  pub_off _ _ (by decide +kernel) pub m

namespace RenderBundleV3

/-- **`SPAR` balance**: the public scheduler parameters are exactly what the codec (11) and the
scan/distribute table (12) of the `PriorCore` blocks of `A`'s trace receive. -/
theorem balancedAt_spar {cb wb : Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)
    {bs : List NativeBlock} (hc : PriorCore A.p NearSpecV3.B0 bs) (hlen : bs.length = A.steps.length + 1)
    (h11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 A.pub)
    (h12 : (R ⟨12, by decide⟩).tr = ProcScanDistPhases.trace bs) :
    R.BalancedAt Sched.B_SPAR := by
  intro m
  rw [R.sum_tables true _ m _ covers_spar_send, R.sum_tables false _ m _ covers_spar_recv, pub_spar_recv]
  have hf0 : (List.range 25).filter (fun _ => false) = [] := by decide
  have hf : (List.range 25).filter (fun t => t == 11 || t == 12) = [11, 12] := by decide
  rw [hf0, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add]
  rw [h11, R.cnt_tf 12 (by decide) false, h12]
  have e1 := codec_sel A.pub _ (prior_cap hc) _ false sparT (rt_spar · · 11 A.pub) m
  have i12 : nearAirV3.tables[12].interactions = ScanDist.table.interactions := rfl
  rw [i12, e1, ssd_count A.hp bs hc _ false sparM row_spar (by simp [sparM, fp_add0, fp_01]) 12 A.pub m,
    ssd_blocks bs (fun b hb => (hc.valid b hb).2)]
  obtain ⟨-, p2, -, -⟩ := sched_pub_counts A m
  rw [p2]
  -- the public records, block by block
  have hpubs := prior_pubs A hc hlen
  have hpar : (Public.schedulerRecords A.p).par =
      bs.flatMap (fun b => pubBlock b.run.tau (instOf b.pub)) := by
    have hPs : A.p.sched.map Sched.instOf = [] ++ bs.map (fun b => instOf b.pub) := by
      rw [← hpubs, List.map_map]; rfl
    have h := flatMap_instAt pubBlock (fun b => instOf b.pub) bs [] (fun i b hi => by
      simpa using prior_tau hc i b hi)
    rw [← hPs] at h
    simp only [List.length_nil] at h
    rw [← h, ← List.range_eq_range']
    have hL : (A.p.sched.map Sched.instOf).length = bs.length := by rw [List.length_map, sched_length A, hlen]
    show ((List.range (A.p.sched.map Sched.instOf).length).flatMap fun τ => _) = _
    rw [hL]
    rfl
  rw [hpar, List.flatMap_map]
  have hperm : (bs.flatMap fun b => (blkOf b).descs.flatMap sparT ++ scanPart (fun row => sparM (fx row)) b ++
      distPart (fun row => sparM (fx row)) b).Perm (recF (bs.flatMap fun b => pubBlock b.run.tau (instOf b.pub))) := by
    rw [recF, List.map_flatMap]
    apply flatMap_perm'
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    have hidx := hc.indexed i b hi
    have hs := prepD0_sched A.hp b.pub (List.mem_iff_getElem?.mpr ⟨i, hidx.1.1⟩)
    exact block_spar b i (hc.valid b hb).2 (ProcPreparedSequence.input_bounds b.pub b.old hs).2.2 hidx.1.2
  have hc3 := hperm.count_eq m
  rw [count_flatMap_app3] at hc3
  rw [List.count_append]
  omega

end RenderBundleV3
end ZkFormal.NearV3.Assembly
