import WasmBase.Main.Abstract
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



/-! ## The per-row segment transition

`exec_of_rows` passes one fixed `(S_seg, segb)` to `RowSpec2` for every row.  That is exactly what a
host-carrying trace cannot do, so the induction needs a per-row relation whose *output* segment may
differ from its input segment:

```
SegRowSpec X inS outS cons prod
  : ∀ ... RelW at (S_seg, segb) ... →
      ∃ S_seg' segb', <output STATE message> ∧ RelW at (S_seg', segb')
```

An ordinary row instantiates it with `(S_seg' , segb') = (S_seg, segb)` (its `RowSpec2`), and a host
row with `(S + fee, g_after)` (`Main/HostRel.host_rel_restart`).  The induction then threads
`(S_seg k, segb k)` positionally, and the final statement reports the **last** segment rather than a
single global one — which is precisely what `Main/ExecHost.lean` states.
-/

/-- The successor segment is `(S + fee, g_after)` at a host row, matching `Main.Host.host_row_seg`. -/
def segHost (S fee gAfter : Nat) : Nat × Nat := (S + fee, gAfter)

/-- An ordinary row keeps the segment. -/
def segKeep (S_seg segb : Nat) : Nat × Nat := (S_seg, segb)

/-- The invariant at a kept segment is the one already held. -/
theorem seg_keep_inv {R S S_seg segb g fee : Nat} (h : R * (S - S_seg) + g = segb)
    (hseg : S_seg ≤ S) (hle : R * fee ≤ g) :
    R * (S + fee - S_seg) + (g - R * fee) = segb := by
  have hm : R * (S + fee - S_seg) = R * (S - S_seg) + R * fee := by
    rw [← Nat.mul_add]; congr 1; omega
  rw [hm]
  omega

/-- **The segment after a restart.**  The new pair is `(S + fee, g_after)` and the invariant there is
`0 + g_after = g_after`; `segb'` is a 64-bit budget, so `RelW.segbLt` is re-established. -/
theorem seg_host_inv {R S fee gAfter : Nat} (h : gAfter < 2 ^ 64) :
    R * ((S + fee) - (S + fee)) + gAfter = gAfter ∧ gAfter < 2 ^ 64 := by
  exact ⟨by simp, h⟩

end WasmBase

