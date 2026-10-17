import NearCompression.TrivariateInitialBranch

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]
local instance : NatCast K := Semiring.natCast

/-- Formal derivative in Y of a bivariate polynomial stored by Y rows. -/
def bivariateYDerivative (rows : List (Poly K)) : List (Poly K) :=
  (List.range (rows.length-1)).map (fun j=>Poly.smul (Nat.cast (j+1) : K) (rows.getD (j+1) Poly.zero))

/-- Actual derivative coefficients, including indices beyond stored rows. -/
theorem bivariate_y_derivative_coefficient (rows : List (Poly K)) (i j : Nat) :
    ((bivariateYDerivative rows).getD j Poly.zero).coeff i=
      (Nat.cast (j+1) : K)*(rows.getD (j+1) Poly.zero).coeff i := by
  by_cases inside : j<rows.length-1
  · simp [bivariateYDerivative,List.getD,inside,Poly.coeff_smul]
  · have outside : rows.length≤j+1 := by omega
    have derivOutside : (bivariateYDerivative rows).length≤j := by simp only [bivariateYDerivative,List.length_map,List.length_range];omega
    have dz : (bivariateYDerivative rows).getD j Poly.zero=Poly.zero := by simp [List.getD,show ¬j<(bivariateYDerivative rows).length by omega]
    have rz : rows.getD (j+1) Poly.zero=Poly.zero := by simp [List.getD,show ¬j+1<rows.length by omega]
    rw [dz,rz]
    change (0:K)=(Nat.cast (j+1) : K)*0
    grind

private theorem small_nat_cast_nonzero (p n : Nat) [IsCharP K p]
    (positive : 0<n) (small : n<p) : (Nat.cast n : K)≠0 := by
  intro zero
  have modular:=(IsCharP.natCast_eq_zero_iff p n).mp zero
  rw [Nat.mod_eq_of_lt small] at modular
  omega

/-- Below the characteristic, zero Y-derivative is equivalent to being
constant in Y. This is not a squarefreeness claim for reducible polynomials. -/
theorem bivariate_y_derivative_zero_iff (p : Nat) [IsCharP K p]
    (rows : List (Poly K)) (height : rows.length≤p) :
    (∀ i j,((bivariateYDerivative rows).getD j Poly.zero).coeff i=0) ↔
      (∀ i j,0<j→(rows.getD j Poly.zero).coeff i=0) := by
  constructor
  · intro zero i j positive
    by_cases inside : j<rows.length
    · have scalar:=small_nat_cast_nonzero (K:=K) p j positive (by omega)
      have h:=zero i (j-1)
      rw [bivariate_y_derivative_coefficient] at h
      have equal : j-1+1=j := by omega
      rw [equal] at h
      rcases Field.of_mul_eq_zero h with cast|coefficient
      · exact False.elim (scalar cast)
      · exact coefficient
    · have outside : rows.length≤j := by omega
      have rz : rows.getD j Poly.zero=Poly.zero := by simp [List.getD,show ¬j<rows.length by omega]
      rw [rz]
      rfl
  · intro constant i j
    rw [bivariate_y_derivative_coefficient,constant i (j+1) (by omega)]
    grind

/-- A Y-dependent polynomial whose stored Y-degree is below characteristic
has a nonzero formal Y-derivative over any field of that characteristic. -/
theorem bivariate_small_y_derivative_nonzero (p : Nat) [IsCharP K p]
    (rows : List (Poly K)) (height : rows.length≤p)
    (dependent : ∃ i j,0<j ∧ (rows.getD j Poly.zero).coeff i≠0) :
    ∃ i j,((bivariateYDerivative rows).getD j Poly.zero).coeff i≠0 := by
  apply Classical.byContradiction
  intro none
  have zero : ∀ i j,((bivariateYDerivative rows).getD j Poly.zero).coeff i=0 := by
    intro i j
    apply Classical.byContradiction
    intro entry
    exact none ⟨i,j,entry⟩
  have constant:=(bivariate_y_derivative_zero_iff p rows height).mp zero
  obtain ⟨i,j,positive,entry⟩:=dependent
  exact entry (constant i j positive)

/-- Concrete field bridge uses the existing proved Fp8 characteristic instance. -/
theorem fp8_small_y_derivative_nonzero (rows : List (Poly Fp8)) (height : rows.length≤P)
    (dependent : ∃ i j,0<j ∧ (rows.getD j Poly.zero).coeff i≠0) :
    ∃ i j,((bivariateYDerivative rows).getD j Poly.zero).coeff i≠0 :=
  bivariate_small_y_derivative_nonzero P rows height dependent

/-- Recorded interpolation screen heights only, not approved protocol parameters. -/
theorem recorded_interpolation_heights_below_characteristic (height : Nat)
    (member : height∈[58,83,116,165,236,379,464]) : height≤P := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
end NearCompression
