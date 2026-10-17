import NearCompression.BivariateTranslation

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Weighted degree <D: every coefficient of X^i Y^j with i+k*j≥D
vanishes. This uses semantic coefficients, so arbitrary zero padding is allowed. -/
def BivariateWeightedDegree (rows : List (Poly K)) (k D : Nat) : Prop :=
  ∀ i j,D≤i+k*j→(rows.getD j Poly.zero).coeff i=0

private theorem product_zero_right (p q : Poly K) (zero : q.IsZero) : (p*q).IsZero := by
  intro i
  have h:=polynomial_order_mul 0 (i+1) p q (by intro j hj;omega) (fun j _=>zero j)
  exact h i (by omega)

/-- Substituting a polynomial of degree at most k preserves the strict
weighted-degree bound. Includes k=0, D=0 and rows beyond the degree budget. -/
theorem bivariate_substitution_degree (rows : List (Poly K)) (curve : Poly K)
    (k D : Nat) (curveDegree : curve.DegLt (k+1))
    (weighted : BivariateWeightedDegree rows k D) :
    (bivariateSubstitute rows curve).DegLt D := by
  induction rows generalizing D with
  | nil => intro i hi;simp [bivariateSubstitute,Poly.zero,Poly.coeff]
  | cons row rest ih =>
    have head : row.DegLt D := by
      intro i hi
      exact weighted i 0 (by simpa using hi)
    have tail : BivariateWeightedDegree rest k (D-k) := by
      intro i j bound
      have expanded : k*(j+1)=k*j+k := by grind
      exact weighted i (j+1) (by rw [expanded];omega)
    have tailDegree:=ih (D-k) tail
    apply Poly.degLt_add head
    by_cases small : D≤k
    · have zero : (bivariateSubstitute rest curve).IsZero := by
        intro i
        exact tailDegree i (by omega)
      exact fun i _=>product_zero_right curve _ zero i
    · have positive : D-k=(D-k-1)+1 := by omega
      rw [positive] at tailDegree
      have product:=Poly.degLt_mul curveDegree tailDegree
      have size : k+(D-k-1)+1=D := by omega
      simpa only [size] using product

/-- Direct coefficient-cutoff formulation used to allocate interpolation
monomials. Rows at or beyond D/k must be formally zero; truncation is explicit. -/
theorem bivariate_weighted_degree_rows (rows : List (Poly K)) (k D : Nat) :
    BivariateWeightedDegree rows k D ↔
      ∀ j,(rows.getD j Poly.zero).DegLt (D-k*j) := by
  constructor
  · intro weighted j i hi
    exact weighted i j (by omega)
  · intro bounds i j hi
    exact bounds j i (by omega)

/-- Root forcing with substitution degree now DERIVED from weighted degree.
The algebraic separation guard still needs an adequate distinct field domain;
interpolant existence/nonzeroness and MCA exception counting are not claimed. -/
theorem bivariate_weighted_multiplicity_zero (rows : List (Poly K)) (curve : Poly K)
    (k D : Nat) (curveDegree : curve.DegLt (k+1))
    (weighted : BivariateWeightedDegree rows k D)
    (centers : List K) (centerDistinct : centers.Nodup) (multiplicity : K→Nat)
    (total : D≤(centers.map multiplicity).sum)
    (sample : List K) (sampleDistinct : sample.Nodup)
    (separation : ∀ a∈centers,
      max (polynomialTranslate (bivariateSubstitute rows curve) a).coeffs.length
        (bivariateSubstitute (bivariateTranslate rows a (curve.eval a))
          (centeredCurve curve a)).coeffs.length≤sample.length)
    (mixed : ∀ a∈centers,BivariateOrder (bivariateTranslate rows a (curve.eval a)) (multiplicity a)) :
    (bivariateSubstitute rows curve).IsZero :=
  bivariate_multiplicity_forces_zero rows curve centers centerDistinct multiplicity D
    (bivariate_substitution_degree rows curve k D curveDegree weighted) total sample sampleDistinct separation mixed
end NearCompression
