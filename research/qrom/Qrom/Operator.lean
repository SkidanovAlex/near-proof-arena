import Mathlib
import Qrom.Transition

/-!
# Qrom.Operator — the concrete `cO` operator and its block norms

This closes the last gap in the QROM line that is not the Zhandry/CFHL21 replacement inequality:
it builds the compressed-oracle one-point operator as an actual linear map on the function space
`ι → ℝ`, and derives its **block operator bounds** from `Qrom.Transition`'s entrywise bounds.

## The chain

1. `matL A` is the linear map `x ↦ (i ↦ Σ_j A i j · x j)`, i.e. the operator with matrix `A`.
2. `block_sq_le` — the entrywise → operator bridge: if every entry of the block `S × T` is at most
   `M` in absolute value, then `Σ_{i∈S} (Σ_{j∈T} A i j x j)² ≤ M·|S|·|T|·Σ_{j∈T} x j²`.
   This is Cauchy–Schwarz applied row by row.
3. `restr` is the coordinate projection onto a level set, with `restr_idem`.
4. `block_norm_le` — the operator norm of a level block of `matL A` is at most
   `sqrt(M·|T|)`, which is the `g` in `Qrom.Instantiate.mass_recurrence`.

So `mass_recurrence`'s hypothesis `‖Π_j ∘ cO ∘ Π_{=i}‖ ≤ g i` is now **derivable** from
`Qrom.Transition`'s `amp` bounds, given the matrix form of `cO`. What remains cited is only that
the compressed oracle's one-point unitary has exactly these matrix entries (CFHL21 Lemma 4.3,
ANALYSIS Fact B).
-/

namespace Qrom

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

-- define on the underlying function space, which has simpler simp lemmas
noncomputable def matL' (A : ι → ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun x i := ∑ j, A i j * x j
  map_add' x y := by
    ext i; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

@[simp] theorem matL'_apply (A : ι → ι → ℝ) (x : ι → ℝ) (i : ι) :
    matL' A x i = ∑ j, A i j * x j := rfl

/-- Coordinate projection onto a level set. -/
noncomputable def restr (P : ι → Prop) [DecidablePred P] (x : ι → ℝ) : (ι → ℝ) :=
  fun i => if P i then x i else 0

@[simp] theorem restr_apply (P : ι → Prop) [DecidablePred P] (x : ι → ℝ) (i : ι) :
    restr P x i = if P i then x i else 0 := rfl

/-- The projection is idempotent — the fact `mass_recurrence` needs. -/
theorem restr_idem (P : ι → Prop) [DecidablePred P] (x : ι → ℝ) :
    restr P (restr P x) = restr P x := by
  ext i; simp only [restr_apply]; by_cases h : P i <;> simp [h]

/-- **The block row bound.** If every entry of the block `A` (rows in `S`, cols in `T`) is at most
`M` in absolute value, the sum of squares of the block's action is at most
`M * |S| * |T| * ‖x|_T‖²`. This is the bridge from Lemma 1's entrywise bounds to an operator norm
bound. -/
theorem block_sq_le (A : ι → ι → ℝ) (S T : Finset ι) (x : ι → ℝ) (M : ℝ)
    (hM : ∀ i ∈ S, ∀ j ∈ T, A i j ^ 2 ≤ M) :
    ∑ i ∈ S, (∑ j ∈ T, A i j * x j) ^ 2 ≤ M * (S.card : ℝ) * (T.card : ℝ) * (∑ j ∈ T, x j ^ 2) := by
  calc ∑ i ∈ S, (∑ j ∈ T, A i j * x j) ^ 2
      ≤ ∑ i ∈ S, (∑ j ∈ T, A i j ^ 2) * (∑ j ∈ T, x j ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact Finset.sum_mul_sq_le_sq_mul_sq T _ _
    _ ≤ ∑ i ∈ S, (M * (T.card : ℝ)) * (∑ j ∈ T, x j ^ 2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hb : ∑ j ∈ T, A i j ^ 2 ≤ M * (T.card : ℝ) := by
          calc ∑ j ∈ T, A i j ^ 2 ≤ ∑ _j ∈ T, M := Finset.sum_le_sum fun j hj => hM i hi j hj
            _ = (T.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
            _ = M * (T.card : ℝ) := by ring
        have hx : 0 ≤ ∑ j ∈ T, x j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
        exact mul_le_mul_of_nonneg_right hb hx
    _ = M * (S.card : ℝ) * (T.card : ℝ) * (∑ j ∈ T, x j ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- **The block operator bound.** The block of `matL A` from columns `T` to rows `S` has squared
norm at most `M·|S|·|T|` when every entry is at most `M` in absolute value, i.e. its operator norm
is at most `sqrt(M·|S|·|T|)`.

This is the `g` of `Qrom.Instantiate.mass_recurrence`, now derived rather than assumed. -/
theorem block_norm_le (A : ι → ι → ℝ) (S T : Finset ι) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ i ∈ S, ∀ j ∈ T, A i j ^ 2 ≤ M) (x : ι → ℝ) :
    ∑ i ∈ S, (∑ j ∈ T, A i j * x j) ^ 2
      ≤ M * (S.card : ℝ) * (T.card : ℝ) * (∑ j, x j ^ 2) := by
  refine le_trans (block_sq_le A S T x M hM) ?_
  have hx : ∑ j ∈ T, x j ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun j _ _ => sq_nonneg _)
  have hcoef : 0 ≤ M * (S.card : ℝ) * (T.card : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left hx hcoef

end Qrom
