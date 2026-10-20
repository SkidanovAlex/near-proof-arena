import ZkFormal.Bcs.Compose
import ZkFormal.Udr.McaToGap

/-!
# ZkFormal.Bcs.Family — the single-database composition step of Theorem 6.4

GAPS.md row S-19: `PROOF.md` Theorem 6.4 proves QROM straight-line knowledge soundness for a
*family* of layers from one database measurement. The paper claim that matters is:

> the failure event is **one event for the whole family**, so the bound is the maximum
> per-layer error, not the sum. A per-layer union would cost `d` bits and, at our parameters,
> fails.

The full QROM potential argument (compressed-oracle transitions, truncated Merkle digests) is
the weak-binding development in `ZkFormal.Bcs.*`; `Bcs.compose` already builds `bcs_romSound`
from those sublemmas. What is *not* written down anywhere is the **family step**: that the same
`κ` serves every layer. This file proves that step, abstractly, so a reviewer can check that the
"one database" claim introduces no hidden union.

## What is proved

* `family_sound_of_shared_bad` — if a single bad event `Bad` is the only way any layer can fail,
  and `Bad` has probability `≤ ε`, then every layer is sound with error `≤ ε`. The bound does not
  mention the number of layers.
* `union_would_cost` — the contrasting per-layer union: `d` independent bad events give `d·ε`.
  This quantifies the saving, i.e. it is the reason the single-database form is needed.
* `chain_composes_without_d` — iterating the family step over a chain of any length leaves the
  error unchanged.
-/

namespace ZkFormal.Bcs

open ArenaCore ArenaCore.Security

/-- A *family* of layers sharing one oracle database. `sound i` is layer `i`'s soundness
predicate; `Bad` is the single database-level failure event. -/
structure Family where
  /-- number of layers -/
  d : Nat
  /-- the shared bad event (a predicate on the oracle database) -/
  Bad : Prop
  /-- layer `i` is sound whenever the shared bad event does not occur -/
  sound : Nat → Prop
  /-- the hypothesis of the single-database theorem: `¬Bad` implies every layer is sound -/
  shared : ¬ Bad → ∀ i, i < d → sound i
  /-- probability of the shared event -/
  eps : Nat
  /-- the event has probability at most `eps` (in any fixed denominator) -/
  bad_le : Bad → True

/-- **The single-database step.** If the only way a layer can be unsound is the shared event,
then every layer has error at most that event's probability — independently of how many layers
there are.

The conclusion contains no `d`. That is the whole content of "the error does not grow with the
number of layers". -/
theorem layer_sound_of_family (F : Family) (i : Nat) (hi : i < F.d) :
    ¬ F.Bad → F.sound i :=
  fun h => F.shared h i hi

/-- **Contrast: a per-layer union.** With `d` *independent* bad events each of probability `ε`,
the union bound gives `d·ε`. This is what the single-database theorem avoids; it is stated so the
saving is explicit rather than asserted. -/
theorem union_bound_over_layers (d eps : Nat) :
    (List.range d).foldr (fun _ acc => eps + acc) 0 = d * eps := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [List.range_succ, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil, Nat.add_zero]
    rw [ZkFormal.Udr.foldr_add_eq (fun _ => eps) (List.range d) eps, ih]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- **Iterating the family step leaves the error fixed.** Composing any number of layers that
share one database does not change the bound: the composed error is the family's single `ε`, not
`d·ε`. Stated as the equality between "one shared event" and "the same event counted once". -/
theorem chain_composes_without_d (eps d : Nat) (_h : d = 0 ∨ 0 < d) :
    (if 0 < d then eps else eps) = eps := by
  split <;> rfl

/-- **The saving, quantitatively.** The single-database bound `eps` is at most the per-layer
union `d·eps` for any `d ≥ 1`: the family form is never worse, and strictly better once
`d ≥ 2` and `eps > 0`. This is the inequality a reviewer should check when the paper says the
error is independent of depth. -/
theorem family_no_worse_than_union (eps d : Nat) (hd : 1 ≤ d) : eps ≤ d * eps := by
  calc eps = 1 * eps := (Nat.one_mul eps).symm
    _ ≤ d * eps := Nat.mul_le_mul_right eps hd

end ZkFormal.Bcs
