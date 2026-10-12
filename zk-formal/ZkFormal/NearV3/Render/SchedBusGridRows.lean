import ZkFormal.NearV3.Render.SchedBusSsdSinc

/-!
# Scan/distribute rows: per-descriptor messages on `SDLX` (both sides) and `SDG`
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render.Ssd SchedSetAll

set_option maxRecDepth 8192 in
theorem param_sdlxs (R : Run) : sdlxsM (fx (Scan.paramRow R)) = [] := by
  simp only [sdlxsM, fx, ProcScanParamPhysical.row_all, ProcScanParamLocal.assignments]; ssd_eval
set_option maxRecDepth 8192 in
theorem param_sdlxr (R : Run) : sdlxrM (fx (Scan.paramRow R)) = [] := by
  simp only [sdlxrM, fx, ProcScanParamPhysical.row_all, ProcScanParamLocal.assignments]; ssd_eval
set_option maxRecDepth 8192 in
theorem param_sdg (R : Run) : sdgM (fx (Scan.paramRow R)) = [] := by
  simp only [sdgM, fx, ProcScanParamPhysical.row_all, ProcScanParamLocal.assignments]; ssd_eval

set_option maxRecDepth 8192 in
theorem header_sdlxs (tv n i sv count left : Nat) : sdlxsM (fx (ProcDistHeader.row tv n i sv count left)) = [] := by
  simp only [sdlxsM, fx, ProcDistHeaderPhysical.row_all, ProcDistHeader.assignments]; ssd_eval
set_option maxRecDepth 8192 in
theorem header_sdg (tv n i sv count left : Nat) : sdgM (fx (ProcDistHeader.row tv n i sv count left)) = [] := by
  simp only [sdgM, fx, ProcDistHeaderPhysical.row_all, ProcDistHeader.assignments]; ssd_eval
set_option maxRecDepth 8192 in
theorem header_sdlxr (tv n i sv count left : Nat) :
    sdlxrM (fx (ProcDistHeader.row tv n i sv count left)) = [F [tv, i, 255, sv, count, left]] := by
  simp only [sdlxrM, fx, ProcDistHeaderPhysical.row_all, ProcDistHeader.assignments, F]; ssd_eval

set_option maxRecDepth 8192 in
theorem shard_sdlxs (tv n sd i x count left budget kp : Nat) :
    sdlxsM (fx (ProcDistShardRow.row tv n sd i x count left budget kp)) =
      [F [tv, if sd = 0 then i else 0, if sd = 0 then 255 else i, x, count, left]] := by
  simp only [sdlxsM]
  simp (disch := decide) only [shard_fx, ProcDistShardRow.core]
  by_cases h : sd = 0 <;> simp only [F, h] <;> ssd_eval
set_option maxRecDepth 8192 in
theorem shard_sdlxr (tv n sd i x count left budget kp : Nat) :
    sdlxrM (fx (ProcDistShardRow.row tv n sd i x count left budget kp)) = [] := by
  simp only [sdlxrM]
  simp (disch := decide) only [shard_fx, ProcDistShardRow.core]; ssd_eval
set_option maxRecDepth 8192 in
theorem shard_sdg (tv n sd i x count left budget kp : Nat) :
    sdgM (fx (ProcDistShardRow.row tv n sd i x count left budget kp)) = [] := by
  simp only [sdgM]
  simp (disch := decide) only [shard_fx, ProcDistShardRow.core]; ssd_eval

set_option maxRecDepth 8192 in
theorem cell_sdlxr (ids : List Nat) (tv n i j sv rr n1 l1 n2 l2 : Nat) (al : Bool) :
    sdlxrM (fx (ProcDistCellRow.row ids tv n i j sv rr n1 l1 n2 l2 al)) = [F [tv, i, j, rr, n2, l2]] := by
  simp only [sdlxrM]
  simp (disch := decide) only [cell_fx, ProcDistCellRow.core]
  simp only [F]; ssd_eval

set_option maxRecDepth 8192 in
theorem cell_sdlxs (ids : List Nat) (tv n i j sv rr n1 l1 n2 l2 : Nat) (al : Bool) :
    sdlxsM (fx (ProcDistCellRow.row ids tv n i j sv rr n1 l1 n2 l2 al)) =
      if i + 1 = n then [] else
        [[Fp.ofNat tv, Fp.ofNat (i + 1), Fp.ofNat j, Fp.ofNat rr, Fp.ofNat n2 + -Fp.ofNat (b2n al),
          Fp.ofNat (l2 - ProcDistCellRow.grant al n1 l1 n2 l2)]] := by
  simp only [sdlxsM]
  simp (disch := decide) only [cell_fx, ProcDistCellRow.core]
  by_cases h : i + 1 = n <;> simp only [h] <;> ssd_eval

set_option maxRecDepth 8192 in
theorem cell_sdg (ids : List Nat) (tv n i j sv rr n1 l1 n2 l2 : Nat) (al : Bool) :
    sdgM (fx (ProcDistCellRow.row ids tv n i j sv rr n1 l1 n2 l2 al)) =
      [[Fp.ofNat tv, Fp.ofNat ((sv * n + rr) % 256 + 256 * ((sv * n + rr) / 256)), Fp.ofNat (b2n al),
        Fp.ofNat (ProcDistCellRow.grant al n1 l1 n2 l2),
        Fp.ofNat ((srcFields ids (sv * n + rr))[0]! + 256 * (srcFields ids (sv * n + rr))[1]!),
        Fp.ofNat (srcFields ids (sv * n + rr))[2]!, Fp.ofNat (srcFields ids (sv * n + rr))[3]!]] := by
  simp only [sdgM]
  simp (disch := decide) only [cell_fx, ProcDistCellRow.core]
  ssd_eval

open ProcScanRequestFactor in
theorem req_grid (R : Run) (c : CReq) (rho jj cv : Nat) :
    sdlxsM (fx (row R c rho jj cv)) = [] ∧ sdlxrM (fx (row R c rho jj cv)) = [] ∧
      sdgM (fx (row R c rho jj cv)) = [] := by
  obtain ⟨-, -, -, hkC, -, -, -, -, -, hs, hr, -⟩ := ProcScanRequestQuietCells.zeros R c rho jj cv
  refine ⟨?_, ?_, ?_⟩
  · simp only [sdlxsM, fx_of hs]; ssd_eval
  · simp only [sdlxrM, fx_of hr]; ssd_eval
  · simp only [sdgM, fx_of hkC]; ssd_eval

end ZkFormal.NearV3.Render.SsdBus
