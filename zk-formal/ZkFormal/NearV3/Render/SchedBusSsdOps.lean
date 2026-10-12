import ZkFormal.NearV3.Render.SchedBusSPAR

/-!
# Scan/distribute table (12): per-block closed forms on `SOP`, `SFIN`, `SPUSH`

* `SOP` sends: one READ per converted request `(16384τ + link, cid + 1, 1, key, key, 0, 0, 0)` (last
  scan row of the request) and one INIT per shard and side `(16384τ + 4096(sd+1) + x, 0, 0, 0, B₀, 0, 0, 0)`;
* `SFIN` receives: one `(16384τ + 4096(sd+1) + x, left, 0)` per shard and side (final budget);
* `SPUSH` sends: one initial push `(τ, key, [key = 0], cid, 64·cid)` per converted request.
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render.Ssd ZkFormal.NearV3.Assembly.CodecDigest
open ProcNativeOldComparisonCapacity ProcDistCellBridge NearSpecV3.Scheduler

theorem range20_last (g : Nat → List (List Fp)) (h : ∀ rho, rho < 19 → g rho = []) :
    (List.range 20).flatMap g = g 19 := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  simp only [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide),
    h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide),
    h 16 (by decide), h 17 (by decide), h 18 (by decide), List.nil_append]

def readMsg (R : Run) (c : CReq) : List Nat := [16384 * R.tau + c.link, c.cid + 1, 1, c.key, c.key, 0, 0, 0]
def pushMsg (R : Run) (c : CReq) : List Nat := [R.tau, c.key, b2n (c.key == 0), c.cid, 64 * c.cid]

theorem scan_sop (b : NativeBlock) :
    scanPart (fun row => sopM (fx row)) b = b.run.conv.map (fun c => F (readMsg b.run c)) := by
  unfold scanPart scanDescs
  split
  · rename_i h
    simp only [List.isEmpty_iff] at h
    simp [h]
  · rw [List.flatMap_cons, List.flatMap_assoc]
    simp only []
    have hp : sopM (fx (Desc.param b.run).row) = [] := param_sop b.run
    rw [hp, List.nil_append, ← flat_single']
    apply flatMap_congr_rt
    intro c _
    rw [List.flatMap_map, range20_last _ (fun rho h19 => by
      rw [req_row_eq _ _ _ (by omega), req_sop, if_neg (by omega)])]
    rw [req_row_eq _ _ _ (by decide), req_sop, if_pos (by decide)]
    rfl

theorem scan_spush (b : NativeBlock) :
    scanPart (fun row => spushM (fx row)) b = b.run.conv.map (fun c => F (pushMsg b.run c)) := by
  unfold scanPart scanDescs
  split
  · rename_i h
    simp only [List.isEmpty_iff] at h
    simp [h]
  · rw [List.flatMap_cons, List.flatMap_assoc]
    simp only []
    have hp : spushM (fx (Desc.param b.run).row) = [] := param_spush b.run
    rw [hp, List.nil_append, ← flat_single']
    apply flatMap_congr_rt
    intro c _
    rw [List.flatMap_map, range20_last _ (fun rho h19 => by
      rw [req_row_eq _ _ _ (by omega), req_spush, if_neg (by omega)])]
    rw [req_row_eq _ _ _ (by decide), req_spush, if_pos (by decide)]
    rfl

theorem scan_sfin (b : NativeBlock) : scanPart (fun row => sfinM (fx row)) b = [] := by
  unfold scanPart scanDescs
  split
  · rfl
  · rw [List.flatMap_cons, List.flatMap_assoc]
    simp only []
    have hp : sfinM (fx (Desc.param b.run).row) = [] := param_sfin b.run
    rw [hp, List.nil_append]
    apply List.flatMap_eq_nil_iff.mpr
    intro c _
    apply List.flatMap_eq_nil_iff.mpr
    intro d hd
    obtain ⟨rho, hr, rfl⟩ := List.mem_map.mp hd
    rw [req_row_eq _ _ _ (List.mem_range.mp hr), req_sfin]

def initMsg (I : Input) (R : Run) (sd i : Nat) : List Nat :=
  [16384 * R.tau + (4096 * (sd + 1) + sX I R sd i), 0, 0, 0, sB I R sd i, 0, 0, 0]
def finMsg (I : Input) (R : Run) (sd i : Nat) : List Nat :=
  [16384 * R.tau + (4096 * (sd + 1) + sX I R sd i), sL I R sd i, 0]

theorem dist_ops (I : Input) (R : Run) :
    (((List.range R.n).map (shardD I R 0)) ++ ((List.range R.n).map (shardD I R 1)) ++
      (grid I R R.n).1).flatMap (fun d => sopM (fx d.row)) =
      (List.range R.n).map (fun i => F (initMsg I R 0 i)) ++ (List.range R.n).map (fun i => F (initMsg I R 1 i)) ∧
    (((List.range R.n).map (shardD I R 0)) ++ ((List.range R.n).map (shardD I R 1)) ++
      (grid I R R.n).1).flatMap (fun d => sfinM (fx d.row)) =
      (List.range R.n).map (fun i => F (finMsg I R 0 i)) ++ (List.range R.n).map (fun i => F (finMsg I R 1 i)) ∧
    (((List.range R.n).map (shardD I R 0)) ++ ((List.range R.n).map (shardD I R 1)) ++
      (grid I R R.n).1).flatMap (fun d => spushM (fx d.row)) = [] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.flatMap_append, List.flatMap_append, List.flatMap_map, List.flatMap_map,
      grid_flat I R (fun d => sopM (fx d.row)) (fun _ _ => []) (fun i j n1 l1 n2 l2 => cell_sop _ _ _ _ _ _ _ _ _ _ _ _)]
    simp only [hdrD, Desc.row, header_sop, List.nil_append, List.flatMap_nil, shardD, shard_sop, ← flat_single',
      List.append_nil]
    simp
    rfl
  · rw [List.flatMap_append, List.flatMap_append, List.flatMap_map, List.flatMap_map,
      grid_flat I R (fun d => sfinM (fx d.row)) (fun _ _ => []) (fun i j n1 l1 n2 l2 => cell_sfin _ _ _ _ _ _ _ _ _ _ _ _)]
    simp only [hdrD, Desc.row, header_sfin, List.nil_append, List.flatMap_nil, shardD, shard_sfin, ← flat_single',
      List.append_nil]
    simp
    rfl
  · rw [List.flatMap_append, List.flatMap_append, List.flatMap_map, List.flatMap_map,
      grid_flat I R (fun d => spushM (fx d.row)) (fun _ _ => []) (fun i j n1 l1 n2 l2 => cell_spush _ _ _ _ _ _ _ _ _ _ _ _)]
    simp [hdrD, Desc.row, header_spush, shardD, shard_spush]

end ZkFormal.NearV3.Render.SsdBus
