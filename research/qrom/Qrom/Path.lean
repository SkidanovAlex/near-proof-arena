import Mathlib
import Qrom.Transition

/-!
# Qrom.Path — ANALYSIS Lemma 2: the path (chain) lemma

Companion to `research/near-compression/weak-binding/ANALYSIS.md` §3, Lemma 2. This is the step
that turns the per-query transition bound (Lemma 1) into the QROM adversary bound
`‖Π_{κ≥K+1} ψ_t‖ ≤ A_t`.

## The abstract statement

Lemma 2 is a lemma about **any** sequence of nonnegative reals `a_s(j)` (the mass at potential
level `≥ j` after `s` queries) satisfying

  `a_{s+1}(j) ≤ a_s(j) + Σ_{i<j} G_{i,j} · a_s(i)`,

with `a_0(j) ≤ Ahat_0(j)`. The conclusion is `a_t(j) ≤ Ahat_t(j)`, where

  `Ahat_t(j) = Σ_{m≥0} C(t,m) · W_m(j)`,  `W_0(0) = 1`, `W_0(j>0) = 0`,
  `W_{m+1}(j) = Σ_{i<j} W_m(i) · G_{i,j}`.

`W_m(j)` is exactly ANALYSIS's chain sum `Σ_{0 = i₀ < … < i_m = j} Π_k G_{i_k,i_{k+1}}`.

**Why this abstraction is faithful.** The compressed-oracle argument supplies the recursion from
Lemma 1 plus the fact that the adversary's unitaries commute with the diagonal projectors.
Nothing else about quantum mechanics enters Lemma 2. Proving it on `ℝ`-valued sequences is
therefore the right formalization, and it is the piece a reviewer most wants checked.

## Results

* `Ahat_step` — `Ahat` satisfies the recursion with **equality** (ANALYSIS step 4, by Pascal's rule
  `C(s+1,m+1) = C(s,m) + C(s,m+1)`).
* `path_bound` — the induction `a ≤ Ahat` over queries (ANALYSIS step 5), giving
  `‖Π_{κ≥K+1} ψ_t‖ ≤ A_t`.

Research package (`Qrom`, Mathlib allowed). `zk-formal` may not depend on Mathlib (DESIGN.md F4),
so a result proved here must be re-proved there before entering a certificate.
-/

namespace Qrom

open scoped BigOperators
open Finset

open scoped BigOperators
open Finset

noncomputable def W (G : Nat → Nat → ℝ) : Nat → Nat → ℝ
  | 0, j => if j = 0 then 1 else 0
  | m + 1, j => ∑ i ∈ Finset.range j, W G m i * G i j

noncomputable def Ahat (G : Nat → Nat → ℝ) (t j : Nat) : ℝ :=
  ∑ m ∈ Finset.range (t + 1), (Nat.choose t m : ℝ) * W G m j

theorem shift (G : Nat → Nat → ℝ) (s j : Nat) :
    ∑ m ∈ Finset.range (s+1), (Nat.choose s m : ℝ) * (∑ i ∈ Finset.range j, G i j * W G m i)
      = ∑ i ∈ Finset.range j, G i j * (∑ m ∈ Finset.range (s+1), (Nat.choose s m : ℝ) * W G m i) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem Ahat_step (G : Nat → Nat → ℝ) (s j : Nat) :
    Ahat G (s+1) j = Ahat G s j + ∑ i ∈ Finset.range j, G i j * Ahat G s i := by
  unfold Ahat
  rw [← shift G s j]
  have hW : ∀ m, (∑ i ∈ Finset.range j, G i j * W G m i) = W G (m+1) j := by
    intro m; rw [W]; exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hW]
  rw [Finset.sum_range_succ' (fun m => (Nat.choose (s+1) m : ℝ) * W G m j)]
  rw [Finset.sum_range_succ' (fun m => (Nat.choose s m : ℝ) * W G m j)]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
  have hpascal : ∀ m ∈ Finset.range (s+1),
      (Nat.choose (s+1) (m+1) : ℝ) * W G (m+1) j
        = (Nat.choose s (m+1) : ℝ) * W G (m+1) j + (Nat.choose s m : ℝ) * W G (m+1) j := by
    intro m _
    rw [Nat.choose_succ_succ']
    push_cast
    ring
  rw [Finset.sum_congr rfl hpascal, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ (fun k => (Nat.choose s (k+1) : ℝ) * W G (k+1) j)]
  have hzero : (Nat.choose s (s+1) : ℝ) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [hzero]
  ring

-- Ahat_nonneg
theorem W_nonneg {G : Nat → Nat → ℝ} (hG : ∀ i j, 0 ≤ G i j) : ∀ m j, 0 ≤ W G m j
  | 0, j => by unfold W; split <;> norm_num
  | m + 1, j => by
      unfold W
      exact Finset.sum_nonneg fun i _ => mul_nonneg (W_nonneg hG m i) (hG i j)

theorem Ahat_nonneg {G : Nat → Nat → ℝ} (hG : ∀ i j, 0 ≤ G i j) (t j : Nat) :
    0 ≤ Ahat G t j := by
  unfold Ahat
  exact Finset.sum_nonneg fun m _ => mul_nonneg (by positivity) (W_nonneg hG m j)

-- The main induction: a s j ≤ Ahat G s j
theorem a_le_Ahat (G : Nat → Nat → ℝ) (hG : ∀ i j, 0 ≤ G i j) :
    ∀ (a : Nat → Nat → ℝ),
    (∀ j, a 0 j ≤ Ahat G 0 j) →
    (∀ s j, a (s+1) j ≤ a s j + ∑ i ∈ Finset.range j, G i j * a s i) →
    ∀ s j, a s j ≤ Ahat G s j := by
  intro a h0 hstep s
  induction s with
  | zero => exact h0
  | succ s ih =>
    intro j
    calc a (s+1) j
        ≤ a s j + ∑ i ∈ Finset.range j, G i j * a s i := hstep s j
      _ ≤ Ahat G s j + ∑ i ∈ Finset.range j, G i j * Ahat G s i := by
          refine add_le_add (ih j) ?_
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_left (ih i) (hG i j)
      _ = Ahat G (s+1) j := (Ahat_step G s j).symm

/-- **Lemma 2 (path lemma), final form.** Under the recursion and nonnegativity hypotheses, every
potential level is bounded by the chain sum. This is ANALYSIS Lemma 2, steps 4–5. -/
theorem path_bound (G : Nat → Nat → ℝ) (hG : ∀ i j, 0 ≤ G i j) (a : Nat → Nat → ℝ)
    (ha0 : ∀ j, a 0 j ≤ Ahat G 0 j)
    (hstep : ∀ s j, a (s+1) j ≤ a s j + ∑ i ∈ Finset.range j, G i j * a s i) :
    ∀ t j, a t j ≤ Ahat G t j :=
  a_le_Ahat G hG a ha0 hstep

end Qrom
