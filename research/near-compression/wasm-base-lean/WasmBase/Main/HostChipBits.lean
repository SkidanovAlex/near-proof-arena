import WasmBase.Main.ExecHost
import WasmBase.Main.HostChipFacts
import WasmBase.Main.RowHostSpec

/-!
# WasmBase.Main.HostChipBits — what the host tables do and do not pin down

`ChipFacts` (`Main/Exec.lean`) is the premise `exec_of_rows` needs: every interaction count of a
chip table is a bit, an inactive row carries none, and an active row satisfies its `RowSpec2`.  This
file asks the same questions of the four host tables, because `exec_of_rows_seg` needs them to
re-run the induction over `wasmBaseHostAir`.

## What holds

* **HOST (22)** — every count is `act` or `act · dir`-like, and since `edae7a53d` the CH channels are
  gated by `act` (`Host.cActPf`, `Host.cActNres`).  So an inactive row emits nothing
  (`host_row_inactive_emits_nothing`) and the counts are bits.  `HostChipFacts`
  (`Main/HostChipFacts.lean`) supplies the row-level facts.
* **HOSTT (24)** — one send with count `v mult`; `mult` is constrained (`hostTab_table_r16` and the
  row-level facts show it is the cached row's flag).
* **HOSTB (25)** — counts are `act · (1 − dir)` and `act · dir`, and `act`/`dir` are boolean, so
  they are bits.

## What does *not* hold, and why it matters

**HOSTO (23) has no constraints at all and counts its two interactions with a free column
`mult`.**  `HostO.table.constraints = []`, and both interactions are counted with `Expr.col
HostO.mult` (`hosto_constraints_nil`, `hosto_counts_are_mult` below).  Nothing in the AIR forces
`mult ≤ 1`, so on an admissible trace a `HOSTO` row may carry count 1, 2, 5, …  `ChipFacts.counts`
therefore does **not** follow from `Holds` for table 23, and neither does the "inactive row carries
nothing" analogue.

This is not a proof gap; it is a property of the AIR as designed.  `HOSTO` is the *witness oracle*
`pq-host-chip` put in the trace so the Wasm-side proof can be stated without the state side
(`results/pq-host-chip/RESULTS.md` §"HOSTO is the response oracle in-trace").  Its multiplicity is
the number of calls the oracle answers, not a bit, so a "counts ≤ 1" premise is the wrong
hypothesis for it.

## Consequence for `wasm_base_exec_host`

`exec_of_rows_seg` takes a per-row `RowSpecSeg` and a per-row gas bound; it does **not** itself
require `ChipFacts`.  That premise enters twice, in the parts of `wasm_base_exec`'s body that:

1. derive the bit-ness used by `msgs_perm` (to turn bus balance into a permutation), and
2. decide which rows are "active" (`rowAct`, i.e. count 1).

For a `HOSTO` row neither is available from `Holds`.  So `wasm_base_exec_host` must either

* (a) restrict the statement to traces whose `HOSTO` rows have `mult ≤ 1` — which is exactly the
  honest witness oracle (one response per call), stated as a trace-level side condition; or
* (b) constrain `mult` in the AIR (`bool (v mult)`), which changes `wasmBaseHostAir` and therefore
  the pinned shape.

(a) is a statement change, (b) is an AIR change.  Both are decisions, not proofs; recorded here so
the choice is explicit rather than discovered mid-proof.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## HOSTO is unconstrained -/

/-- **`HOSTO` has no constraints.** -/
theorem hosto_constraints_nil : HostO.table.constraints = [] := rfl

/-- **`HOSTO`'s two counts are the free column `mult`.** -/
theorem hosto_counts_are_mult :
    (HostO.table.inters.map fun i => i.count) = [Expr.col HostO.mult, Expr.col HostO.mult] := rfl

/-- **`HOSTO`'s multiplicity is not bounded by any constraint.**  With no constraints, every row of
`HOSTO` satisfies them vacuously whatever `mult` is, so "counts are bits" cannot follow from
`Holds` for table 23.  This is why `wasm_base_exec_host` needs either a trace-level `mult ≤ 1`
condition or an AIR change; see the header. -/
theorem hosto_no_count_bound (r : Nat) (tr : Trace) (pub : List F) :
    ∀ e ∈ HostO.table.constraints, e.eval (tr.row pub 23 r) = (0 : F) := by
  intro e he
  rw [hosto_constraints_nil] at he
  exact absurd he (List.not_mem_nil)

end WasmBase
