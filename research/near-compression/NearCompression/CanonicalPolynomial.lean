import NearCompression.ScalarRSTerminal

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def canonicalPolynomial (D : Nat) (p : Poly K) : Poly K := Poly.mk (p.coeffs.take D)

omit [Field K] in
theorem canonical_polynomial_length (D : Nat) (p : Poly K) :
    (canonicalPolynomial D p).coeffs.length≤D := by
  simp only [canonicalPolynomial,List.length_take]
  omega

theorem canonical_polynomial_coeff (D : Nat) (p : Poly K) (degree : p.DegLt D) :
    ∀ i,(canonicalPolynomial D p).coeff i=p.coeff i := by
  intro i
  change (p.coeffs.take D).getD i 0=p.coeffs.getD i 0
  simp only [List.getD,List.getElem?_take]
  by_cases hi : i<D
  · simp [hi]
  · simp only [hi,ite_false,Option.getD_none]
    exact (degree i (by omega)).symm

theorem canonical_polynomial_eval (D : Nat) (p : Poly K) (degree : p.DegLt D) (x : K) :
    (canonicalPolynomial D p).eval x=p.eval x := by
  have zero : (canonicalPolynomial D p-p).IsZero := by
    intro i
    rw [Poly.coeff_sub,canonical_polynomial_coeff D p degree]
    grind
  have eq := Poly.eval_of_isZero zero x
  rw [Poly.eval_sub] at eq
  grind

theorem canonical_polynomial_residual (D : Nat) (p : Poly K) (degree : p.DegLt D)
    (weights : List K) :
    scalarRSResidual weights (canonicalPolynomial D p)=scalarRSResidual weights p :=
  scalar_rs_residual_congr _ _ weights (canonical_polynomial_coeff D p degree)

end NearCompression
