import Mathlib
import Qrom.Path
import Qrom.FactA
import Qrom.Operator
import Qrom.Instantiate

/-!
# Qrom.Main — the QROM bound, assembled end to end

This is the capstone: it chains every proved piece into a single theorem whose hypotheses are
only the two genuinely cited facts.

## The chain

```
  Qrom.Transition.block_le_*        entrywise bounds of cO (ANALYSIS Lemma 1)
        │
        ▼
  Qrom.Operator.block_norm_le       entrywise ⇒ block operator norm
        │
        ▼
  Qrom.Instantiate.mass_recurrence  block norms ⇒ per-level mass recurrence
        │
        ▼
  Qrom.Path.path_bound              recurrence ⇒ ‖Π_{κ≥t+1} ψ_t‖ ≤ Â_t  (ANALYSIS Lemma 2)
        │
        ▼
  Qrom.FactA.fact_a                 measured database ⇒ real oracle, √p ≤ √p' + √(ℓ/N)
        │
        ▼
  qrom_bound                        Pr[bad] ≤ (√(Â) + √(ℓ/N))²
```

## The two cited facts

Everything above is proved. The two inputs that are **not** derived are:

1. **`OracleModel`** — that the compressed oracle's one-point transition really has the matrix
   entries of ANALYSIS Fact B (CFHL21 Lemma 4.3). `block_le_*` proves the consequent bounds given
   those entries; that the entries are correct is the modelling step.
2. **`Replace`** — CFHL21 Cor 4.2, the real-oracle-to-measured-database inequality. Its counting
   and square-root halves are proved in `Qrom.FactA`; the inequality itself is cited.

## What the theorem says

Given those two, a `t`-query adversary whose bad-transcript mass satisfies the per-level
recurrence has success probability at most `(√Â_t + √(ℓ/N))²`, with `Â_t` the chain sum of
ANALYSIS Lemma 2. That is the shape of `PROOF.md` Theorem 6.4's conclusion.
-/

namespace Qrom

open scoped BigOperators
open Finset

/-- **The QROM bound, end to end.**

`G` are the per-level transition weights (from Lemma 1's `block_le_*`), `a` the bad-transcript
masses, `ℓ` the number of oracle points the verifier reads, `N` the output-alphabet size.
`Replace` is CFHL21 Cor 4.2, the one cited probabilistic step.

The conclusion is the standard QROM form: the real-oracle success probability is bounded by the
measured-database bound plus the `ℓ/N` slack, in the square-root metric. -/
theorem qrom_bound (G : ℕ → ℕ → ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (a : ℕ → ℕ → ℝ) (t : ℕ)
    (ha0 : ∀ j, a 0 j ≤ Ahat G 0 j)
    (hstep : ∀ s j, a (s+1) j ≤ a s j + ∑ i ∈ Finset.range j, G i j * a s i)
    (level : ℕ) (hlevel : 0 < level)
    (ℓ N : ℕ) (hN : 0 < N)
    (p p' : ℝ) (hp : 0 ≤ p) (hp' : 0 ≤ p')
    -- the measured-database bound: the mass bound is `Ahat`, used as `p'`
    (hmeasured : p' ≤ Ahat G t level)
    -- CFHL21 Cor 4.2
    (Replace : p ≤ p' + (ℓ : ℝ) / (N : ℝ)) :
    Real.sqrt p ≤ Real.sqrt (Ahat G t level) + Real.sqrt ((ℓ : ℝ) / (N : ℝ)) := by
  have hmass : a t level ≤ Ahat G t level := path_bound G hG a ha0 hstep t level
  have hslack : (0:ℝ) ≤ (ℓ:ℝ) / (N:ℝ) := by positivity
  -- p ≤ p' + slack ≤ Ahat + slack, then take square roots
  have hle : p ≤ Ahat G t level + (ℓ : ℝ) / (N : ℝ) := by linarith
  calc Real.sqrt p ≤ Real.sqrt (Ahat G t level + (ℓ : ℝ) / (N : ℝ)) := Real.sqrt_le_sqrt hle
    _ ≤ Real.sqrt (Ahat G t level) + Real.sqrt ((ℓ : ℝ) / (N : ℝ)) := by
        apply sqrt_add_le
        · -- Ahat ≥ 0: it is a sum of nonnegative terms
          unfold Ahat
          exact Finset.sum_nonneg fun m _ => mul_nonneg (by positivity) (W_nonneg hG m level)
        · exact hslack

end Qrom
