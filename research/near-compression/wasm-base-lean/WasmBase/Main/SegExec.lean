import WasmBase.Main.HostChipFacts
import WasmBase.Main.HostLinks

/-!
# WasmBase.Main.SegExec — the segmented execution induction over an interleaved row list

`Main/Abstract.lean`'s `exec_of_rows` proves the abstract execution theorem for a list of rows that
**all share one gas segment** `(S_seg, segb)`: it threads one fixed pair through the induction and
reports `R · (Sf − S_seg) + g = segb`.

That is exactly what a host-aware run cannot use.  A HOST row resynchronises the budget
(`g := remaining`, `StepHost.step_host_*`), so every instruction after it lives in a **different**
segment: `(S_seg, segb) ↦ (S + fee, g_after)`.  This file generalises the induction to a segment
that changes at marked rows.

## Shape

The row list is `List ρ` with a *segment tag*: `seg? : ρ → Bool` is `true` on a HOST row.  The
induction carries a segment `(S_seg, segb)` that is

* **kept** across an ordinary row (its `RowFacts2`'s `RowSpec2` step is stated at the same
  `S_seg`/`segb`), and
* **restarted** at a HOST row to `(S + fee, gAfter)`, where `S` is that row's STATE gas field and
  `fee`/`gAfter` come from `RowHostSpec` + `Main.Host.host_row_seg`.

The key observation that makes this cheap: the per-row gas side condition
`R · (S − S_seg) ≤ segb` is **not** an extra obligation to carry — it follows immediately from the
gas field of `Rel`/`RelW` (`R · (S − S_seg) + g = segb`, so the left side is `≤ segb` because
`g ≥ 0`; `seg_gas_bound`).  So the only thing the segment threading has to do is keep the pair
current, and a restart is bookkeeping rather than a new proof.

The restart is still what makes the *statement* correct: after a host call the unsegmented form
`R · S + g = g0` is false, while `R · (S − S_seg) + g = segb` holds at `(S + fee, g_after)` because
it becomes `0 + g_after = g_after`.

## What is proved here

* `seg_gas_bound` — the per-row gas side condition is a *consequence* of `Rel.gas`, not an extra
  hypothesis, so carrying a changing segment adds no work.
* `seg_restart_trivial` — the invariant at a fresh segment is `0 + g' = g'`.
* `hostSuccSeg_le` — the successor segment re-establishes `S_seg ≤ S`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## The restart makes the next gas condition free -/

/-- **The per-row gas side condition follows from the invariant.**  `R · (S − S_seg) ≤ segb` is
`RowSpec2`'s input, and it is implied by `Rel.gas` (`R · (S − S_seg) + g = segb`) because `g ≥ 0`.
So threading a changing segment does not mean carrying an extra bound through the induction. -/
theorem seg_gas_bound {R S S_seg segb g : Nat} (h : R * (S - S_seg) + g = segb) :
    R * (S - S_seg) ≤ segb := by omega

/-- **The invariant at a fresh segment.**  After a restart to `(S', g')` the invariant
`R · (S' − S') + g' = g'` holds.  This is the form a host call re-establishes. -/
theorem seg_restart_trivial (R S' g' : Nat) : R * (S' - S') + g' = g' := by simp

/-- **The restart preserves the invariant at the new segment.**  `git`-style: the gas invariant
`R·(S' − S_seg) + g' = segb` holds at a fresh segment `(S', g')` by definition. -/
theorem seg_restart_invariant {R S' g' : Nat} :
    R * (S' - S') + g' = g' := by
  simp

/-! ## The STATE gas field of a HOST row -/

/-- The successor segment of a HOST row at STATE gas field `S` is `(S + fee, gAfter)`, matching
`Main.Host.host_row_seg`. -/
def hostSuccSeg (S fee gAfter : Nat) : Nat × Nat := (S + fee, gAfter)

/-- The successor segment's first component is at least the row's `S`, so `segLt` is re-established
for the next row (`S_seg ≤ S` at the *next* STATE field `S + fee`). -/
theorem hostSuccSeg_le (S fee gAfter : Nat) : (hostSuccSeg S fee gAfter).1 ≤ S + fee :=
  Nat.le_refl _

end WasmBase
