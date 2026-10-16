import NearCompression.DerivativeBezoutDenominator

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Polynomial parameter expressions specialize at every base-field point. -/
theorem polynomial_rational_polynomial_specializes (p : Poly K) (z : K) :
    PolynomialRationalValueAt (polynomialRationalOfPolynomial p) z (p.eval z) := by
  refine ⟨.ofPolynomial (formalPolynomial p),rfl,?_,?_⟩
  · change (Poly.C (1:K)).eval z≠0
    rw [Poly.eval_C];exact fun zero=>Field.zero_ne_one zero.symm
  · change p.eval z*((Poly.C (1:K)).eval z)⁻¹=p.eval z
    rw [Poly.eval_C];grind

/-- A nonvanishing common denominator suffices for every numerator. -/
theorem polynomial_rational_quotient_specializes (num den : Poly K) (z : K)
    (safe : den.eval z≠0) :
    PolynomialRationalValueAt
      (polynomialRationalOfPolynomial num*(polynomialRationalOfPolynomial den)⁻¹)
      z (num.eval z*(den.eval z)⁻¹) :=
  polynomial_rational_value_mul _ _ z _ _ (polynomial_rational_polynomial_specializes num z)
    (polynomial_rational_value_inv _ z _ (polynomial_rational_polynomial_specializes den z) safe)

/-- Coordinatewise partial specialization supplies a polynomial with the same
coefficient-list length, preserving trailing-zero representations. -/
theorem rational_polynomial_specialization_exists (p : Poly (PolynomialRational K)) (z : K)
    (safe : ∀ i,∃ value,PolynomialRationalValueAt (p.coeff i) z value) :
    ∃ q : Poly K,RationalPolynomialSpecializes p q z := by
  cases p with | mk cs =>
    induction cs with
    | nil => exact ⟨Poly.zero,.nil⟩
    | cons c cs ih =>
      obtain ⟨v,hv⟩:=safe 0
      obtain ⟨q,hq⟩:=ih (fun i=>safe (i+1))
      exact ⟨Poly.mk (v::q.coeffs),.cons hv hq⟩

/-- The explicit derivative determinant alone protects the entire bounded
certificate. No product of one denominator per coefficient is necessary. -/
theorem irreducible_derivative_certificate_specializes
    (characteristic : Nat) [IsCharP K characteristic]
    (ps : Nat→Poly K) (p : Poly (PolynomialRational K)) (d : Nat)
    (pc : ∀ i,polynomialRationalOfPolynomial (ps i)=p.coeff i)
    (irreducible : PolynomialIrreducible p) (degree : p.DegLt (d+1))
    (leading : p.coeff d≠0) (positive : 0<d) (small : d<characteristic)
    (z : K) (safe : (derivativeSharedDenominator ps d).eval z≠0) :
    ∃ (A B : Poly (PolynomialRational K)) (C D : Poly K),
      PolynomialCoeffEq (A*p+B*polynomialDerivative p) (Poly.C 1) ∧
      RationalPolynomialSpecializes A C z ∧ RationalPolynomialSpecializes B D z := by
  obtain ⟨A,B,ad,bd,certificate,coordinates⟩:=irreducible_derivative_shared_certificate
    characteristic ps p d pc irreducible degree leading positive small
  have values : ∀ r, r<2*d-1 → ∃ v,
      PolynomialRationalValueAt (bezoutCoefficientVector A B (d-1) r) z v := by
    intro r inside
    rw [coordinates r inside]
    exact ⟨_,polynomial_rational_quotient_specializes _ _ z safe⟩
  have av : ∀ i,∃ v,PolynomialRationalValueAt (A.coeff i) z v := by
    intro i
    by_cases inside : i<d-1
    · have h:=values i (by omega)
      simpa only [bezoutCoefficientVector,ite_eq_left inside] using h
    · rw [ad i (by omega)]
      exact ⟨0,rational_coefficient_specializes 0 z⟩
  have bv : ∀ i,∃ v,PolynomialRationalValueAt (B.coeff i) z v := by
    intro i
    by_cases inside : i<d
    · have h:=values (d-1+i) (by omega)
      have outside : ¬d-1+i<d-1 := by omega
      simpa only [bezoutCoefficientVector,ite_eq_right outside,Nat.add_sub_cancel_left] using h
    · rw [bd i (by omega)]
      exact ⟨0,rational_coefficient_specializes 0 z⟩
  obtain ⟨C,cs⟩:=rational_polynomial_specialization_exists A z av
  obtain ⟨D,ds⟩:=rational_polynomial_specialization_exists B z bv
  exact ⟨A,B,C,D,certificate,cs,ds⟩

/-- Every root of a safely specialized source is smooth outside the single
source-degree-controlled derivative denominator. -/
theorem irreducible_shared_denominator_root_smooth
    (characteristic : Nat) [IsCharP K characteristic]
    (ps : Nat→Poly K) (p : Poly (PolynomialRational K)) (d : Nat)
    (pc : ∀ i,polynomialRationalOfPolynomial (ps i)=p.coeff i)
    (irreducible : PolynomialIrreducible p) (degree : p.DegLt (d+1))
    (leading : p.coeff d≠0) (positive : 0<d) (small : d<characteristic)
    (q : Poly K) (z a : K) (specializes : RationalPolynomialSpecializes p q z)
    (safe : (derivativeSharedDenominator ps d).eval z≠0) (root : q.eval a=0) :
    (polynomialDerivative q).eval a≠0 := by
  obtain ⟨A,B,C,D,cert,cs,ds⟩:=irreducible_derivative_certificate_specializes
    characteristic ps p d pc irreducible degree leading positive small z safe
  exact rational_bezout_specialized_root_smooth p A B q C D z a cert specializes cs ds root

/-- The same denominator condition supplies the actual finite Hensel lift;
no independently assumed smoothness or safe certificate coefficients remain. -/
theorem irreducible_shared_denominator_hensel_lift
    (characteristic : Nat) [IsCharP K characteristic]
    (ps : Nat→Poly K) (p : Poly (PolynomialRational K)) (d : Nat)
    (pc : ∀ i,polynomialRationalOfPolynomial (ps i)=p.coeff i)
    (irreducible : PolynomialIrreducible p) (degree : p.DegLt (d+1))
    (leading : p.coeff d≠0) (positive : 0<d) (small : d<characteristic)
    (rows : List (Poly K)) (z a : K) (n : Nat)
    (specializes : RationalPolynomialSpecializes p (initialYPolynomial rows) z)
    (safe : (derivativeSharedDenominator ps d).eval z≠0)
    (root : (initialYPolynomial rows).eval a=0) :
    (curveHenselLift rows a n).coeff 0=a ∧
    (curveHenselLift rows a n).DegLt (n+1) ∧
    PolynomialOrder (bivariateSubstitute rows (curveHenselLift rows a n)) (n+1) := by
  obtain ⟨A,B,C,D,cert,cs,ds⟩:=irreducible_derivative_certificate_specializes
    characteristic ps p d pc irreducible degree leading positive small z safe
  exact rational_certificate_hensel_lift p A B rows C D z a n cert specializes cs ds root
/-- Singular specialized roots have a source-degree budget, replacing the
older presentation-dependent product-of-denominators bound. -/
theorem irreducible_shared_denominator_singular_count
    (characteristic : Nat) [IsCharP K characteristic]
    (ps : Nat→Poly K) (p : Poly (PolynomialRational K)) (d D : Nat)
    (pc : ∀ i,polynomialRationalOfPolynomial (ps i)=p.coeff i)
    (irreducible : PolynomialIrreducible p) (degree : p.DegLt (d+1))
    (leading : p.coeff d≠0) (positive : 0<d) (small : d<characteristic)
    (sourceDegree : ∀ i,(ps i).DegLt (D+1))
    (q : K→Poly K) (specializes : ∀ z,RationalPolynomialSpecializes p (q z) z)
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun z=>∃ a : K,(q z).eval a=0 ∧ (polynomialDerivative (q z)).eval a=0)≤(2*d-1)*D := by
  apply Nat.le_trans _ (irreducible_derivative_denominator_exception_count characteristic ps p d D
    pc irreducible degree leading positive small sourceDegree sample distinct)
  apply count_mono
  intro z bad
  obtain ⟨a,root,singular⟩:=bad
  apply Classical.byContradiction
  intro safe
  exact irreducible_shared_denominator_root_smooth characteristic ps p d pc irreducible
    degree leading positive small (q z) z a (specializes z) safe root singular
end NearCompression
