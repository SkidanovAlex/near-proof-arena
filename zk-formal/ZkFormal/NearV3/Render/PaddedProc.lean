import ZkFormal.NearV3.Render.RowTraffic
import ZkFormal.NearV3.Candidates.ProcActualNativeComplete

/-!
# Aligned process-table generator (`nearAirV3` table 13, `Proc.tableB`) over all runs

`procTraceV3 rs` is the array-backed concatenated process table of all scheduler runs `rs`
(`Candidates/ProcConcatGeometry`: every run's value records `procVs R`, the tail row, padding),
at the scheduler's shared height `2^22` (`22 ≡ 1 (mod 3)`, the cap).  Local legality for the
boundary-repaired constraints is `ProcActualNativeComplete.list_local` (native runs
`ActualRun.run I τ = .ok R`, `τ` consecutive from `0`, capacity); the traffic is the exact
trace-free row traffic `rowsTraffic Proc.interactions (procCell rs) 22 t pub` (`RowTraffic`):
every interaction reads the current row only.
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Candidates.ShaHeight

/-- Cell `c` of row `r` of the concatenated honest process table. -/
def procCell (rs : List Run) (r c : Nat) : Nat := (ProcConcatGeometry.atRow rs r).cell c

def procTraceV3 (rs : List Run) : Trace Fp :=
  rowsTrace 22 (mkTab (2 ^ 22) Proc.width (procCell rs))

theorem pv_cell_ge (X : PV) (c : Nat) (hc : Proc.width ≤ c) : X.cell c = 0 := by
  simp only [Proc.width] at hc
  unfold PV.cell
  repeat rw [if_neg (by omega)]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem proc_interactions_current :
    Proc.interactions.all (fun i => i.exprs.all currentOnly) = true := by decide +kernel

theorem proc_currentOnly : CurrentOnly Proc.tableB.interactions := by
  intro i hi e he
  exact List.all_eq_true.mp (List.all_eq_true.mp proc_interactions_current i hi) e he

theorem boundaryRepair_eq : ProcBoundaryRepair.table = Proc.tableB := rfl

/-- **`sprV3` aligned completeness over all runs** (boundary-repaired `Proc.tableB`). -/
theorem proc_v3_aligned_complete (rs : List Run)
    (hr : ∀ R ∈ rs, ∃ I : Input,
      NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length = some I.p ∧
      ActualRun.run I R.tau = .ok R)
    (hfirst : ∀ R rest, rs = R :: rest → R.tau = 0)
    (ht : ∀ pre R S post, rs = pre ++ R :: S :: post → S.tau = R.tau + 1)
    (hcap : (ProcConcatGeometry.rows rs).length + 1 ≤ 2 ^ 22) (t : Nat) (pub : List Fp) :
    TableLocal Proc.tableB (procTraceV3 rs) t pub ∧
    TableTraffic Proc.tableB.interactions (procTraceV3 rs) t pub
      (rowsTraffic Proc.tableB.interactions (procCell rs) 22 t pub) ∧
    (procTraceV3 rs).log t % 3 = 1 := by
  have hcells : ∀ r, r < 2 ^ 22 → ∀ c, (procTraceV3 rs).cell t r c = Fp.ofNat (procCell rs r c) :=
    fun r hr c => rowsTrace_cells 22 _ _ (fun r c h => pv_cell_ge _ c h) t r hr c
  have hl : (ProcConcatGeometry.trace rs).log t = (procTraceV3 rs).log t := rfl
  have hc : ∀ r, r < (ProcConcatGeometry.trace rs).height t → ∀ c,
      (ProcConcatGeometry.trace rs).cell t r c = (procTraceV3 rs).cell t r c := by
    intro r hr c
    rw [hcells r hr c]; rfl
  have hL := ProcActualNativeComplete.list_local rs hr hfirst ht hcap t pub
  rw [boundaryRepair_eq] at hL
  exact ⟨tableLocal_congr_rows hl hc hL,
    rowFn_traffic _ proc_currentOnly (procCell rs) _ t 22 pub rfl hcells,
    show 22 % 3 = 1 from rfl⟩

end ZkFormal.NearV3.Render
