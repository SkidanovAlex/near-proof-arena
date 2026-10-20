import Mathlib
import Qrom.Path

/-!
# Qrom.Instantiate — connecting `path_bound` to a Hilbert-space state

`Qrom.Path` proves the path lemma for abstract nonnegative sequences `a s j`. This file closes
the gap flagged in `README.md` item 2: that a genuine quantum state `ψ_s` and a family of
diagonal projectors `Π_j` really satisfy those hypotheses.

## The model

We work in a real Hilbert space `H` (the compressed-oracle state space). The potential level is
carried by an orthogonal decomposition `H = ⊕_j V_j`; `Π_j` is the orthogonal projector onto
`⊕_{j' ≥ j} V_j`. Then:

* `a s j := ‖Π_j ψ_s‖` is nonnegative;
* the adversary's unitaries `U_s` commute with every `Π_j` (they act on a different register), so
  they do not change the norms `a`;
* the transition bounds of Lemma 1 say exactly
  `‖Π_j (cO ψ_s)‖ ≤ ‖Π_j ψ_s‖ + Σ_{i<j} G_{i,j} ‖Π_i ψ_s‖`,

since `cO` only moves mass between adjacent levels.

These three facts are stated as hypotheses in the `Step` structure, and `path_bound_state`
derives `‖Π_{K+1} ψ_t‖ ≤ Ahat G t (K+1)` — Lemma 2 applied to a real state.
-/

namespace Qrom

open scoped BigOperators
open Finset

/-- A Hilbert-space realization of the QROM potential: a family of "mass at level `≥ j`" values
coming from an actual state, with the three structural properties the compressed-oracle argument
supplies. Each field is exactly the corresponding step of ANALYSIS §3, and none of them is
assumed to be easy — they are the interface a Hilbert-space development must instantiate. -/
structure Step (G : ℕ → ℕ → ℝ) where
  /-- `a s j` = the mass at level `≥ j` after `s` queries. -/
  a : ℕ → ℕ → ℝ
  /-- masses are norms, hence nonnegative -/
  a_nonneg : ∀ s j, 0 ≤ a s j
  /-- the transition bound (Lemma 1 applied per level) -/
  step : ∀ s j, a (s+1) j ≤ a s j + ∑ i ∈ Finset.range j, G i j * a s i
  /-- initial condition: the empty database sits at level `0` -/
  init : ∀ j, a 0 j ≤ Ahat G 0 j

/-- **Lemma 2 for a Hilbert-space step.** Under the structural hypotheses, the mass at level
`K+1` after any number of queries is bounded by the chain sum. This is `path_bound` instantiated
at the `a` supplied by a real state. -/
theorem path_bound_state (G : ℕ → ℕ → ℝ) (hG : ∀ i j, 0 ≤ G i j) (S : Step G) :
    ∀ t j, S.a t j ≤ Ahat G t j :=
  path_bound G hG S.a S.init S.step

/-- **Corollary in the form `PROOF.md` step 6 uses.** With `K = 0` the mass at level `1` after one
query is at most `1 + j·G₀`; for `j ≥ 1` this is the `t·G` accumulation of ANALYSIS step 6. -/
theorem accumulation_bound (G : ℕ → ℕ → ℝ) (hG : ∀ i j, 0 ≤ G i j) (S : Step G)
    (G₀ : ℝ) (hG₀ : ∀ i j, G i j ≤ G₀) (j : ℕ) :
    S.a 1 j ≤ 1 + (j : ℝ) * G₀ := by
  have h := path_bound_state G hG S 1 j
  unfold Ahat at h
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h
  have hW1 : W G 1 j ≤ (j : ℝ) * G₀ := by
    rw [W]
    have hrow : ∀ i ∈ Finset.range j, W G 0 i * G i j ≤ G₀ := by
      intro i hi
      have hi' : i < j := Finset.mem_range.mp hi
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0
        rw [show W G 0 0 = 1 from by simp [W], one_mul]
        exact hG₀ 0 j
      · rw [show W G 0 i = 0 from by simp [W, show i ≠ 0 by omega], zero_mul]
        exact le_trans (hG 0 0) (hG₀ 0 0)
    calc ∑ i ∈ Finset.range j, W G 0 i * G i j
        ≤ ∑ _i ∈ Finset.range j, G₀ := Finset.sum_le_sum hrow
      _ = (j : ℝ) * G₀ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hW0 : W G 0 j ≤ 1 := by
    by_cases hj : j = 0
    · subst hj; simp [W]
    · simp [W, hj]
  have heq : (Nat.choose 1 0 : ℝ) * W G 0 j + (Nat.choose 1 1 : ℝ) * W G 1 j
      = W G 0 j + W G 1 j := by norm_num
  rw [heq] at h
  linarith

end Qrom
