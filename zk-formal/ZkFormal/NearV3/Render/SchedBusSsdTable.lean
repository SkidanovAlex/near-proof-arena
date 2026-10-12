import ZkFormal.NearV3.Render.SchedBusSsdRows

/-!
# Scan/distribute table traffic by blocks

`ssd_count`: on the honest merged trace `ProcScanDistPhases.trace bs`, the count of a message on a bus
whose row traffic is `M (cells)` is its count in `M` over the rows; `ssd_blocks`: the rows are every
block's scan descriptors, then every block's shard rows and grid descriptors.
-/
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render.Ssd ZkFormal.NearV3.Assembly.CodecDigest
open ProcNativeOldComparisonCapacity ProcDistCellBridge
set_option autoImplicit false

theorem ssd_physical (rows : Array (Array Nat)) (hcap : rows.size ≤ 2 ^ 22) (b : Nat) (s : Bool)
    (M : (Nat → Fp) → List (List Fp))
    (hM : ∀ tr t r pub, rowTraffic ScanDist.table.interactions tr t r pub b s = M (tr.cell t r))
    (hz : M (fun _ => 0) = []) (t : Nat) (pub : List Fp) :
    (List.range (2 ^ 22)).flatMap (fun r => rowTraffic ScanDist.table.interactions
      (SchedHeight.trace rows distPad) t r pub b s) = rows.toList.flatMap (fun row => M (fx row)) := by
  simp only [hM]
  rw [show 2 ^ 22 = rows.size + (2 ^ 22 - rows.size) by omega, List.range_add, List.flatMap_append,
    List.flatMap_map]
  have hzz : (List.range (2 ^ 22 - rows.size)).flatMap (fun j => M
      ((SchedHeight.trace rows distPad).cell t (rows.size + j))) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    rw [ProcDistCmpPhysical.cells_padding rows _ (by omega)]
    exact hz
  rw [hzz, List.append_nil, ← ProcCodecConcatTraffic.row_lookup rows, List.flatMap_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro r hr
  rw [ProcDistCmpPhysical.cells_active rows r (List.mem_range.mp hr)]
  rfl

theorem ssd_count {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp : NearSpecV3.prepD0 cb hint = .ok p) {B : Nat} (bs : List NativeBlock) (hc : PriorCore p B bs)
    (b : Nat) (s : Bool) (M : (Nat → Fp) → List (List Fp))
    (hM : ∀ tr t r pub, rowTraffic ScanDist.table.interactions tr t r pub b s = M (tr.cell t r))
    (hz : M (fun _ => 0) = []) (t : Nat) (pub m : List Fp) :
    tableBusCount ScanDist.table.interactions (ProcScanDistPhases.trace bs) t pub b s m =
      ((ProcScanDistPhases.rows bs).toList.flatMap (fun row => M (fx row))).count m := by
  have hcap : (ProcScanDistPhases.rows bs).size ≤ 2 ^ 22 := by
    have := (ProcScanDistPhases.capacity hp bs hc).2; omega
  have h := ssd_physical (ProcScanDistPhases.rows bs) hcap b s M hM hz t pub
  rw [tableBusCount_eq]
  exact congrArg (fun xs => xs.count m) h

/-- Per-block scan part and distribute part of a row-message function. -/
def scanPart (G : Array Nat → List (List Fp)) (b : NativeBlock) : List (List Fp) :=
  (scanDescs b.run).flatMap fun d => G d.row

def distPart (G : Array Nat → List (List Fp)) (b : NativeBlock) : List (List Fp) :=
  (((List.range b.run.n).map (shardD (ProcPreparedSequence.input b.pub b.old) b.run 0)) ++
    ((List.range b.run.n).map (shardD (ProcPreparedSequence.input b.pub b.old) b.run 1)) ++
    (grid (ProcPreparedSequence.input b.pub b.old) b.run b.run.n).1).flatMap fun d => G d.row

theorem ssd_blocks (bs : List NativeBlock) (hn : ∀ b ∈ bs, b.run.n ≤ 64) (G : Array Nat → List (List Fp)) :
    (ProcScanDistPhases.rows bs).toList.flatMap G = bs.flatMap (scanPart G) ++ bs.flatMap (distPart G) := by
  unfold ProcScanDistPhases.rows ProcScanDistPhases.scanRows ProcScanDistPhases.distRows
  rw [List.toList_toArray, List.flatMap_append, List.flatMap_assoc, List.flatMap_assoc]
  congr 1
  · apply flatMap_congr_rt
    intro b _
    rw [scan_rows, List.flatMap_map]; rfl
  · apply flatMap_congr_rt
    intro b hb
    rw [(dist_rows _ _ _ (distribution_eq b (hn b hb))).1]
    simp only [distPart, List.flatMap_append, List.flatMap_map]

section
variable (I : Input) (R : Run)

/-- Grid messages when the cell messages do not depend on the endpoint state. -/
theorem cells_flat (G : Desc → List (List Fp)) (i : Nat) (H : Nat → List (List Fp))
    (hG : ∀ j n1 l1 n2 l2, G (.cell I.ids R.tau R.n i j (sender I R i) (receiver I R j) n1 l1 n2 l2 (cAl I R i j)) = H j)
    (g : Array Nat) (ri : Array (Nat × Nat)) (se : Nat × Nat) :
    ∀ k, (cells I R i ([], g, ri, se) k).1.flatMap G = (List.range k).flatMap H
  | 0 => by simp [cells]
  | k + 1 => by
    rw [cells_succ, List.range_succ, List.flatMap_append, ← cells_flat G i H hG g ri se k]
    simp only [cstep, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, hG]

theorem grid_flat (G : Desc → List (List Fp)) (H : Nat → Nat → List (List Fp))
    (hG : ∀ i j n1 l1 n2 l2, G (.cell I.ids R.tau R.n i j (sender I R i) (receiver I R j) n1 l1 n2 l2 (cAl I R i j)) = H i j) :
    ∀ m, (grid I R m).1.flatMap G =
      (List.range m).flatMap fun i => G (hdrD I R i) ++ (List.range R.n).flatMap (H i)
  | 0 => by simp [grid]
  | m + 1 => by
    rw [grid_succ, List.range_succ, List.flatMap_append, ← grid_flat G H hG m]
    simp only [gstep]
    rw [cells_app, List.flatMap_append, List.flatMap_append,
      cells_flat I R G m (H m) (fun j n1 l1 n2 l2 => hG m j n1 l1 n2 l2)]
    simp

end

end ZkFormal.NearV3.Render.SsdBus
