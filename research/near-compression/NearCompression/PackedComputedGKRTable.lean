import NearCompression.PackedSourceExecution
import NearCompression.RecoveredGKRTable

/-! The GKR table decoder and source transform describe the same padded table.
These identities do not establish extraction of coefficients from a Merkle root. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem lower_bounded_congr (n : Nat) (a b : Nat → K)
    (same : ∀ i,i<2^n → a i=b i) (j : Nat) : lowerZeta n a j=lowerZeta n b j := by
  induction n generalizing a b j with
  | zero => exact same 0 (by decide)
  | succ n ih =>
    simp only [lowerZeta]
    split
    · apply ih
      intro i hi
      exact same (2*i) (by rw [Nat.pow_succ]; omega)
    · apply ih
      intro i hi
      rw [same (2*i) (by rw [Nat.pow_succ]; omega),
        same (2*i+1) (by rw [Nat.pow_succ]; omega)]

/-- Decoding the actual mutable source coefficients recovers each original
packed cell, including zero-filled columns in a partial lane. -/
theorem packed_computed_gkr_table (n p width group : Nat) (table : Nat → Nat → K)
    (row col : Nat) (rowBound : row<2^n) (colBound : col<2^p) :
    recoveredGKRTable n p (packedComputedPolynomial n p width group table) row col=
      genericPackedColumn p width group col table row := by
  unfold recoveredGKRTable
  rw [lower_bounded_congr (n+p) _ _ (packed_computed_coefficient n p width group table)]
  rw [lower_zeta_mobius]
  · exact generic_packed_values_index n p width group row col table rowBound
  · rw [Nat.pow_add]
    have h := Nat.mul_le_mul_left (2^n) (show col+1≤2^p by omega)
    rw [Nat.mul_add,Nat.mul_one] at h
    omega

/-- Coefficientwise binding of an extracted polynomial suffices to identify
its decoded table. Pointwise proximity alone is deliberately not substituted. -/
theorem bound_polynomial_gkr_table (n p width group : Nat) (table : Nat → Nat → K)
    (polynomial : Poly K)
    (bound : ∀ i,i<2^(n+p) → polynomial.coeff i=
      (packedComputedPolynomial n p width group table).coeff i)
    (row col : Nat) (rowBound : row<2^n) (colBound : col<2^p) :
    recoveredGKRTable n p polynomial row col=genericPackedColumn p width group col table row := by
  have same : recoveredGKRTable n p polynomial row col=
      recoveredGKRTable n p (packedComputedPolynomial n p width group table) row col :=
    lower_bounded_congr (n+p) _ _ bound _
  exact same.trans (packed_computed_gkr_table n p width group table row col rowBound colBound)

/-- The actual computed source polynomial answers the GKR current/next slot
functional without a caller-supplied Mobius coefficient identity. -/
theorem packed_computed_gkr_functional (n p width group : Nat) (table : Nat → Nat → K)
    (rowpoint left right : Nat → K) (gamma : K) :
    coefficientTableFunctional (n+p) [gkrUniversalTableWeight n p rowpoint left right gamma]
      [packedComputedPolynomial n p width group table]=
    gkrInputFunctional (p+1) left right gamma
      (gkrTableSlots n p (fun row col => genericPackedColumn p width group col table row) rowpoint) := by
  apply gkr_universal_weight_functional n p _ _ _ rowpoint left right gamma
  intro i hi
  exact packed_computed_coefficient n p width group table i hi

end NearCompression
