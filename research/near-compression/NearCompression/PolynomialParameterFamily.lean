import NearCompression.SharedDenominatorSpecialization
import NearCompression.TrivariateInitialBranch

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- A polynomial in Y whose coefficients are explicit polynomials in Z,
embedded into the constructed rational-function field. -/
def polynomialParameterFamily (rows : List (Poly K)) : Poly (PolynomialRational K) :=
  Poly.mk (rows.map polynomialRationalOfPolynomial)

def polynomialParameterSpecialize (rows : List (Poly K)) (z : K) : Poly K :=
  Poly.mk (rows.map (fun p=>p.eval z))

/-- Coefficient extraction commutes with formal embedding, including indices
outside the list and explicit trailing-zero coefficients. -/
theorem polynomial_parameter_family_coefficient (rows : List (Poly K)) (i : Nat) :
    polynomialRationalOfPolynomial (rows.getD i Poly.zero)=
      (polynomialParameterFamily rows).coeff i := by
  induction rows generalizing i with
  | nil =>
    apply (polynomial_rational_of_polynomial_eq_iff _ _).mpr
    intro j;cases j <;> rfl
  | cons p rows ih => cases i with
    | zero => rfl
    | succ i => exact ih i

/-- Explicit polynomial coefficient data automatically satisfies the partial
specialization interface at every point; there are no source poles. -/
theorem polynomial_parameter_family_specializes (rows : List (Poly K)) (z : K) :
    RationalPolynomialSpecializes (polynomialParameterFamily rows)
      (polynomialParameterSpecialize rows z) z := by
  induction rows with
  | nil => exact .nil
  | cons p rows ih => exact .cons (polynomial_rational_polynomial_specializes p z) ih

/-- Bivariate source data now has a singular-point bound with no independent
coefficient-specialization premise. -/
theorem polynomial_parameter_family_singular_count
    (characteristic : Nat) [IsCharP K characteristic] (rows : List (Poly K)) (d D : Nat)
    (irreducible : PolynomialIrreducible (polynomialParameterFamily rows))
    (degree : (polynomialParameterFamily rows).DegLt (d+1))
    (leading : (polynomialParameterFamily rows).coeff d≠0)
    (positive : 0<d) (small : d<characteristic)
    (sourceDegree : ∀ i,(rows.getD i Poly.zero).DegLt (D+1))
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun z=>∃ a : K,(polynomialParameterSpecialize rows z).eval a=0 ∧
      (polynomialDerivative (polynomialParameterSpecialize rows z)).eval a=0)≤(2*d-1)*D :=
  irreducible_shared_denominator_singular_count characteristic (fun i=>rows.getD i Poly.zero)
    (polynomialParameterFamily rows) d D (polynomial_parameter_family_coefficient rows)
    irreducible degree leading positive small sourceDegree (polynomialParameterSpecialize rows)
    (polynomial_parameter_family_specializes rows) sample distinct

/-- Dense trivariate specialization has precisely the initial Y polynomial
obtained by specializing the explicit X=0 coefficient rows. -/
theorem trivariate_initial_parameter_specialization (rows : List (List (Poly K))) (z : K) :
    polynomialParameterSpecialize (trivariateInitialRows rows) z=
      initialYPolynomial (denseTrivariateSpecialize rows z) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have head : (row.getD 0 Poly.zero).eval z=(Poly.mk (row.map (fun p=>p.eval z))).coeff 0 := by
      cases row <;> rfl
    have tail:=congrArg Poly.coeffs ih
    change Poly.mk ((row.getD 0 Poly.zero).eval z::_)=Poly.mk ((Poly.mk (row.map (fun p=>p.eval z))).coeff 0::_)
    rw [head]
    exact congrArg (fun cs=>Poly.mk ((Poly.mk (row.map (fun p=>p.eval z))).coeff 0::cs)) tail

/-- The source-specialization premise of the Hensel theorem is discharged
from actual dense trivariate data. Irreducibility here is explicitly of the
initial polynomial, not of the whole trivariate source. -/
theorem trivariate_parameter_denominator_hensel_lift
    (characteristic : Nat) [IsCharP K characteristic] (rows : List (List (Poly K))) (d : Nat)
    (irreducible : PolynomialIrreducible (polynomialParameterFamily (trivariateInitialRows rows)))
    (degree : (polynomialParameterFamily (trivariateInitialRows rows)).DegLt (d+1))
    (leading : (polynomialParameterFamily (trivariateInitialRows rows)).coeff d≠0)
    (positive : 0<d) (small : d<characteristic)
    (z a : K) (n : Nat)
    (safe : (derivativeSharedDenominator (fun i=>(trivariateInitialRows rows).getD i Poly.zero) d).eval z≠0)
    (root : (initialYPolynomial (denseTrivariateSpecialize rows z)).eval a=0) :
    (curveHenselLift (denseTrivariateSpecialize rows z) a n).coeff 0=a ∧
    (curveHenselLift (denseTrivariateSpecialize rows z) a n).DegLt (n+1) ∧
    PolynomialOrder (bivariateSubstitute (denseTrivariateSpecialize rows z)
      (curveHenselLift (denseTrivariateSpecialize rows z) a n)) (n+1) := by
  apply irreducible_shared_denominator_hensel_lift characteristic
    (fun i=>(trivariateInitialRows rows).getD i Poly.zero)
    (polynomialParameterFamily (trivariateInitialRows rows)) d
    (polynomial_parameter_family_coefficient _) irreducible degree leading positive small
    (denseTrivariateSpecialize rows z) z a n _ safe root
  rw [←trivariate_initial_parameter_specialization]
  exact polynomial_parameter_family_specializes _ z
end NearCompression
