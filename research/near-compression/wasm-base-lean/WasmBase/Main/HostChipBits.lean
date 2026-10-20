import WasmBase.Main.ExecHost
import WasmBase.Main.HostChipFacts
import WasmBase.Main.RowHostSpec

/-!
# WasmBase.Main.HostChipBits — which host tables touch the buses the induction counts

`ChipFacts` (`Main/Exec.lean`) constrains tables 1-14 of `wasmBaseAir`.  For `wasm_base_exec_host`
the AIR is `wasmBaseHostAir` (26 tables; 22-25 appended).  This file records exactly what the
induction needs from the four host tables, and which of those facts hold.

## The requirement, precisely

`exec_of_rows` needs "every relevant interaction count is a bit" in only two places:

1. `msgs_perm` turns bus **balance** into a message **permutation** — for the STATE bus (0) and the
   CH bus (2), the only buses whose messages the induction permutes;
2. `rowAct` is defined as "count = 1", so deciding row activity needs bit-ness on those same buses.

So the premise is needed **only on buses 0 and 2**, not on the host buses 208-210.

## What touches buses 0 and 2

Only the HOST table.  HOSTO, HOSTT and HOSTB touch none of them:

* `HOST` (22): `stateIn`/`stateOut` on bus 0 with count `act`, and CH receives/sends on bus 2 with
  counts `pf j` / `nres` — all bits, the last two since `edae7a53d` added `Host.cActPf` /
  `Host.cActNres` (`host_row_inactive_emits_nothing`);
* `HOSTO` (23): only `HOSTQ` (208, receive) and `HOSTR` (209, send);
* `HOSTT` (24): only `HOSTT` (9, receive);
* `HOSTB` (25): only `HOSTB` (210) and `BYTE` (4).

## `HOSTO.mult` is unconstrained, and harmless

`HostO.table.constraints = []` and both of its interactions are counted with the free column `mult`
(`hosto_constraints_nil`, `hosto_counts_are_mult`).  Nothing forces `mult ≤ 1`.

**This does not affect `wasm_base_exec_host`.**  `HOSTO` is the witness oracle that stands in for
the state side (`pq-host-chip/RESULTS.md`); its multiplicity is the number of calls it answers, so
`mult > 1` is the correct semantics and constraining it would be wrong.  Because `HOSTO` touches
neither bus 0 nor bus 2 (`hosto_avoids_state_ch`), the induction never reads that count.

(An earlier revision of this file claimed this blocked the instantiation.  It does not: the
requirement is per-bus, and `HOSTO` is on the wrong buses for it.)
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
`HOSTO` satisfies them vacuously whatever `mult` is.  Harmless for the induction: see
`hosto_avoids_state_ch`. -/
theorem hosto_no_count_bound (r : Nat) (tr : Trace) (pub : List F) :
    ∀ e ∈ HostO.table.constraints, e.eval (tr.row pub 23 r) = (0 : F) := by
  intro e he
  rw [hosto_constraints_nil] at he
  exact absurd he (List.not_mem_nil)

/-! ## Which host tables touch the buses the induction counts -/

/-- **The induction counts buses STATE (0) and CH (2) only.**  This is the predicate the segment
theorem's `ChipFacts` analogue needs, and it is what makes `HOSTO.mult` irrelevant. -/
def touchesStateOrCh (T : Table) : Prop :=
  (T.inters.filter fun i => i.bus = busState ∨ i.bus = busStk) ≠ []

/-- **`HOSTO` touches neither STATE nor CH.** -/
theorem hosto_avoids_state_ch : ¬ touchesStateOrCh HostO.table := by
  unfold touchesStateOrCh; decide

/-- **`HOSTT` touches neither STATE nor CH.** -/
theorem hosttab_avoids_state_ch : ¬ touchesStateOrCh HostTab.table := by
  unfold touchesStateOrCh; decide

/-- **`HOSTB` touches neither STATE nor CH.** -/
theorem hostb_avoids_state_ch : ¬ touchesStateOrCh HostB.table := by
  unfold touchesStateOrCh; decide

/-- **Only `HOST` touches them**, and there its counts are `act`, `pf j` and `nres` — bits, the
latter two by `edae7a53d`'s gating constraints. -/
theorem host_touches_state_ch : touchesStateOrCh Host.table := by
  unfold touchesStateOrCh; decide

end WasmBase
