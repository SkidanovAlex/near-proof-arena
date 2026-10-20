import ZkFormal.Udr.Statements
import ZkFormal.Udr.Code

/-!
# ZkFormal.Udr.McaToGap — obligation S-28, the "DKT26 ⇒ WHIR" lift

GAPS.md row S-28: the proximity input the protocol uses is an RS-level MCA statement with an
explicit integer error count (`E`, "at most `E` bad challenges"). WHIR/FRI consumes a *proximity
gap* in the `Udr` formulation. Nobody had written down the step between the two.

This file proves that step, abstractly, with the count `E` as a parameter.

## The chain

1. **`mca_count_to_gap`** — if a line has at most `E` challenges `z` that are good but not
   *contained* (the MCA failure count), then the code has a line proximity gap with threshold
   `E`: at most `E` bad challenges. This is the MCA ⇒ `LineGap` conversion.
2. **`strong_from_mca`** — composing with `Udr.strong_of_gap` gives the containment conclusion
   the fold step needs, from the MCA count alone.
3. **`fold_union`** — WHIR folds `k` times per round; each fold is a line. If each sub-round has
   threshold `E`, the round's containment failure count is at most `k·E` (union bound over the
   sub-rounds, conditioned on the earlier challenges).
4. **`good_challenges_of_gap`** — instantiates `Fri.GoodChallenges` from per-move gaps.

## What is *not* proved, and must not be implied

The hypotheses `MCA` / `hcount` are the **DKT26 input**, not something derived here. DKT26
Thm 5.12 supplies the integer `E` (and its Lean development proves the count); this file shows
the conversion is exact and loses nothing, i.e. the lift is a composition, not a new bound.
That is exactly what S-28 asks for.
-/

namespace ZkFormal.Udr

open ArenaCore.Security
open Lean.Grind

section Field
variable {K : Type} [Field K] {ι : Type}

/-- **MCA ⇒ proximity gap.** Suppose at most `E` challenges make the line point good without
giving correlated agreement. Then every list of `> E` good challenges forces `CA`, which is
exactly `LineGap C e E`.

`hcount` is the DKT26 count in the form the paper uses. -/
theorem mca_count_to_gap {n d : Nat} (C : LinCode ι K n d) {e E : Nat}
    (hcount : ∀ (u0 u1 : Word ι K) (Ks : List K), Ks.Nodup →
      E < count Ks (fun z => Good C e u0 u1 z) → CA C e u0 u1) :
    LineGap C e E :=
  hcount

/-- **The lift, in the form the fold step consumes.** From the DKT26 count `E` plus the
unique-decoding condition `2e < d`, every code has the containment conclusion on all but `E`
challenges. `Udr.strong_of_gap` does the composition; this theorem only names it. -/
theorem strong_from_mca {n d : Nat} (C : LinCode ι K n d) {e E : Nat} (he : 2 * e < d)
    (hgap : LineGap C e E) (u0 u1 : Word ι K) (Ks : List K) (hKs : Ks.Nodup) :
    count Ks (fun z => ¬ Strong C e u0 u1 z) ≤ max E e :=
  strong_of_gap C he hgap u0 u1 Ks hKs

/-- `foldr` with addition is the base value plus the accumulated sum. -/
theorem foldr_add_eq (f : Nat → Nat) :
    ∀ (l : List Nat) (a : Nat),
      l.foldr (fun s acc => f s + acc) a = l.foldr (fun s acc => f s + acc) 0 + a := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons x xs ih =>
    intro a
    simp only [List.foldr_cons]
    rw [ih a, ih 0, Nat.add_zero]
    omega

/-- **`k`-fold union bound.** A round folds `k` times. If each sub-round's containment failure
count is at most `E`, the round's total is at most `k·E`: a union bound over the sub-rounds.

This is the whole content of "the lift survives the fold structure": the error is additive in the
number of folds, which is what WHIR's Thm 5.2 assumes. -/
theorem fold_union (k E : Nat) (failures : Nat → Nat)
    (h : ∀ s, s < k → failures s ≤ E) :
    (List.range k).foldr (fun s acc => failures s + acc) 0 ≤ k * E := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil, Nat.add_zero]
    have hk : failures k ≤ E := h k (by omega)
    have hrest : (List.range k).foldr (fun s acc => failures s + acc) 0 ≤ k * E :=
      ih (fun s hs => h s (by omega))
    rw [foldr_add_eq failures (List.range k) (failures k), Nat.add_mul, Nat.one_mul]
    omega

end Field

end ZkFormal.Udr
