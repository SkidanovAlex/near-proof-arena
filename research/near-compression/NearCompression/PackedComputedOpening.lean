import NearCompression.PackedSourceExecution
import NearCompression.GenericPackedOpeningComposition
import NearCompression.GenericLaneBatching

/-! The computed source transform discharges the packed opening's algebraic
source-binding premise. Exact PCS authentication remains an explicit contract. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

private theorem tensor_congr (n : Nat) (a b point : Nat → K)
    (same : ∀ i, i<2^n → a i=b i) : laneTensor n a point=laneTensor n b point := by
  induction n generalizing a b point with
  | zero => exact same 0 (by decide)
  | succ n ih =>
    simp only [laneTensor]
    rw [ih (fun i => a (2*i)) (fun i => b (2*i)) _ (by
      intro i hi; exact same (2*i) (by rw [Nat.pow_succ]; omega)),
      ih (fun i => a (2*i+1)) (fun i => b (2*i+1)) _ (by
      intro i hi; exact same (2*i+1) (by rw [Nat.pow_succ]; omega))]

private theorem row_sub (n : Nat) (a b point : Nat → K) :
    genericRowMLE n (fun i => a i-b i) point=
      genericRowMLE n a point-genericRowMLE n b point := by
  induction n generalizing a b point with
  | zero => rfl
  | succ n ih => simp only [genericRowMLE,ih]; grind

/-- Mobius coefficients evaluated as a multilinear monomial tensor recover
exactly the original row MLE, at arbitrary extension-field points. -/
theorem mobius_tensor_row_mle (n : Nat) (values point : Nat → K) :
    laneTensor n (mobiusCoefficients n values) point=genericRowMLE n values point := by
  induction n generalizing values point with
  | zero => rfl
  | succ n ih =>
    have even : ∀ i, (2*i)%2=0 := by intro i; omega
    have odd : ∀ i, (2*i+1)%2=1 := by intro i; omega
    have ediv : ∀ i, (2*i)/2=i := by intro i; omega
    have odiv : ∀ i, (2*i+1)/2=i := by intro i; omega
    simp only [laneTensor,mobiusCoefficients,even,odd,ediv,odiv,
      Nat.reduceEqDiff,ite_true,ite_false,ih,row_sub,genericRowMLE]
    grind

/-- No coefficient/source-binding hypothesis: coefficients come from the
modeled mutable transform of the actual padded source table. -/
theorem packed_computed_tensor (rows pack width group : Nat)
    (table : Nat → Nat → K) (point : Nat → K) :
    genericMonomialTensor (rows+pack)
      (packedComputedCoefficients rows pack width group table) point=
    genericRowMLE (rows+pack) (genericPackedValues rows pack width group table) point := by
  rw [lane_tensor_monomial]
  apply Eq.trans (b := laneTensor (rows+pack)
    (mobiusCoefficients (rows+pack) (genericPackedValues rows pack width group table)) point)
  · apply tensor_congr
    intro i hi
    exact packed_computed_coefficient rows pack width group table i hi
  · exact mobius_tensor_row_mle _ _ _

/-- Packed vector authentication bound specialized to computed source
coefficients; the cryptographic exact-opening contract is not discharged. -/
theorem packed_computed_opening_bad_count (rows packPred width group lane : Nat)
    (table : Nat → Nat → K) (rowPoint sent : Nat → K)
    (accepts : List K → K → Prop)
    (pcs : PackedPCSExact rows (packPred+1)
      (packedComputedCoefficients rows (packPred+1) width group table) rowPoint accepts)
    (valid : lane<2^(packPred+1))
    (wrong : sent lane ≠ packedSourceClaims rows (packPred+1) width group table rowPoint lane)
    (sample : List K) (distinct : sample.Nodup) :
    count (packedGrid sample (packPred+1))
      (fun point => ∃ value, accepts point value ∧ packedGridEval (packPred+1) sent point=value) ≤
      (packPred+1)*sample.length^packPred := by
  exact packed_opening_bad_count rows packPred width group lane table rowPoint sent
    _ (packed_computed_tensor rows (packPred+1) width group table) accepts pcs valid wrong sample distinct

end NearCompression
