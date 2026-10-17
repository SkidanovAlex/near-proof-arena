import NearCompression.RationalFunctionSpecialization

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Base-field constants specialize everywhere. -/
theorem rational_coefficient_specializes (c z : K) :
    PolynomialRationalValueAt (polynomialRationalCoefficientMap.toFun c) z c := by
  refine ⟨.ofPolynomial (formalPolynomial (Poly.C c)),rfl,?_,?_⟩
  · change (Poly.C (1:K)).eval z≠0
    rw [Poly.eval_C];exact fun zero=>Field.zero_ne_one zero.symm
  · change (Poly.C c).eval z*((Poly.C (1:K)).eval z)⁻¹=c
    rw [Poly.eval_C,Poly.eval_C]
    grind

inductive RationalCoefficientSpecialization (z : K) : List (PolynomialRational K) → List K → Prop
  | nil : RationalCoefficientSpecialization z [] []
  | cons {r c rs cs} : PolynomialRationalValueAt r z c →
      RationalCoefficientSpecialization z rs cs → RationalCoefficientSpecialization z (r::rs) (c::cs)

/-- Coefficient specialization of a polynomial in the algebraic variable Y.
The witness lists preserve coefficient positions and explicit zero padding. -/
def RationalPolynomialSpecializes (p : Poly (PolynomialRational K)) (q : Poly K) (z : K) : Prop :=
  RationalCoefficientSpecialization z p.coeffs q.coeffs

/-- Horner evaluation commutes with partial coefficient specialization. -/
theorem rational_polynomial_eval_specializes (p : Poly (PolynomialRational K)) (q : Poly K)
    (z a : K) (specializes : RationalPolynomialSpecializes p q z) :
    PolynomialRationalValueAt (p.eval (polynomialRationalCoefficientMap.toFun a)) z (q.eval a) := by
  cases p with | mk ps => cases q with | mk qs =>
    change RationalCoefficientSpecialization z ps qs at specializes
    induction specializes with
    | nil => exact rational_coefficient_specializes 0 z
    | @cons r c rs cs head tail ih =>
      exact polynomial_rational_value_add _ _ z _ _ head
        (polynomial_rational_value_mul _ _ z _ _ (rational_coefficient_specializes a z) ih)

/-- Derivative evaluation also specializes; no field homomorphism defined
at every rational function is assumed. -/
theorem rational_polynomial_derivative_specializes (p : Poly (PolynomialRational K)) (q : Poly K)
    (z a : K) (specializes : RationalPolynomialSpecializes p q z) :
    PolynomialRationalValueAt ((polynomialDerivative p).eval (polynomialRationalCoefficientMap.toFun a))
      z ((polynomialDerivative q).eval a) := by
  cases p with | mk ps => cases q with | mk qs =>
    change RationalCoefficientSpecialization z ps qs at specializes
    induction specializes with
    | nil => exact rational_coefficient_specializes 0 z
    | @cons r c rs cs head tail ih =>
      change PolynomialRationalValueAt
        ((Poly.mk rs+Poly.X*polynomialDerivative (Poly.mk rs)).eval (polynomialRationalCoefficientMap.toFun a))
        z ((Poly.mk cs+Poly.X*polynomialDerivative (Poly.mk cs)).eval a)
      simp only [Poly.eval_add,Poly.eval_mul,Poly.eval_X]
      exact polynomial_rational_value_add _ _ z _ _
        (rational_polynomial_eval_specializes (Poly.mk rs) (Poly.mk cs) z a tail)
        (polynomial_rational_value_mul _ _ z _ _ (rational_coefficient_specializes a z) ih)

private theorem coefficient_equal_eval {F : Type} [Field F] (p q : Poly F)
    (same : PolynomialCoeffEq p q) (a : F) : p.eval a=q.eval a := by
  have zero : (p-q).IsZero := by intro i;rw [Poly.coeff_sub,same i];grind
  have entry:=Poly.eval_of_isZero zero a
  rw [Poly.eval_sub] at entry
  grind

/-- A rational-function Bezout certificate protects every root after safe
specialization of the polynomial and the two certificate polynomials. -/
theorem rational_bezout_specialized_root_smooth
    (p A B : Poly (PolynomialRational K)) (q C D : Poly K) (z a : K)
    (certificate : PolynomialCoeffEq (A*p+B*polynomialDerivative p) (Poly.C 1))
    (ps : RationalPolynomialSpecializes p q z)
    (aspec : RationalPolynomialSpecializes A C z)
    (bspec : RationalPolynomialSpecializes B D z)
    (root : q.eval a=0) : (polynomialDerivative q).eval a≠0 := by
  have pe:=rational_polynomial_eval_specializes p q z a ps
  have ae:=rational_polynomial_eval_specializes A C z a aspec
  have be:=rational_polynomial_eval_specializes B D z a bspec
  have de:=rational_polynomial_derivative_specializes p q z a ps
  have identity:=coefficient_equal_eval _ _ certificate (polynomialRationalCoefficientMap.toFun a)
  rw [Poly.eval_add,Poly.eval_mul,Poly.eval_mul,Poly.eval_C] at identity
  have specialized:=polynomial_rational_value_add _ _ z _ _
    (polynomial_rational_value_mul _ _ z _ _ ae pe)
    (polynomial_rational_value_mul _ _ z _ _ be de)
  rw [identity] at specialized
  have numeric:=polynomial_rational_value_unique _ z _ _ specialized (rational_coefficient_specializes 1 z)
  intro singular
  rw [root,singular] at numeric
  have zeroone : (0:K)=1 := by grind
  exact Field.zero_ne_one zeroone

/-- Irreducibility and the characteristic budget supply the certificate.
The remaining per-point hypothesis is safe coefficient specialization. -/
theorem rational_irreducible_specialization_certificate (characteristic : Nat) [IsCharP K characteristic]
    (p : Poly (PolynomialRational K)) (d : Nat) (irreducible : PolynomialIrreducible p)
    (degree : p.DegLt (d+1)) (leading : p.coeff d≠0)
    (positive : 0<d) (small : d<characteristic) :
    ∃ A B : Poly (PolynomialRational K),
      PolynomialCoeffEq (A*p+B*polynomialDerivative p) (Poly.C 1) ∧
      ∀ (q C D : Poly K) (z a : K), RationalPolynomialSpecializes p q z →
        RationalPolynomialSpecializes A C z → RationalPolynomialSpecializes B D z →
        q.eval a=0 → (polynomialDerivative q).eval a≠0 := by
  obtain ⟨A,B,certificate⟩:=irreducible_derivative_bezout characteristic p d irreducible degree leading positive small
  exact ⟨A,B,certificate,fun q C D z a ps aspec bspec root=>
    rational_bezout_specialized_root_smooth p A B q C D z a certificate ps aspec bspec root⟩

private theorem initial_eval (rows : List (Poly K)) (a : K) :
    (bivariateSubstitute rows (Poly.C a)).coeff 0=(initialYPolynomial rows).eval a := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [bivariateSubstitute,Poly.coeff_add]
    rw [polynomial_order_product_coefficient (Poly.C a) (bivariateSubstitute rest (Poly.C a)) 0 0
      (by intro i hi;omega) (by intro i hi;omega)]
    change row.coeff 0+a*(bivariateSubstitute rest (Poly.C a)).coeff 0=
      row.coeff 0+a*(initialYPolynomial rest).eval a
    rw [ih]

/-- A safely specialized certificate supplies the operational Hensel slope
and the existing finite lift, rather than assuming smoothness separately. -/
theorem rational_certificate_hensel_lift (p A B : Poly (PolynomialRational K))
    (rows : List (Poly K)) (C D : Poly K) (z a : K) (n : Nat)
    (certificate : PolynomialCoeffEq (A*p+B*polynomialDerivative p) (Poly.C 1))
    (ps : RationalPolynomialSpecializes p (initialYPolynomial rows) z)
    (aspec : RationalPolynomialSpecializes A C z)
    (bspec : RationalPolynomialSpecializes B D z)
    (root : (initialYPolynomial rows).eval a=0) :
    (curveHenselLift rows a n).coeff 0=a ∧
    (curveHenselLift rows a n).DegLt (n+1) ∧
    PolynomialOrder (bivariateSubstitute rows (curveHenselLift rows a n)) (n+1) := by
  apply hensel_finite_lift rows a _ _ n
  · rwa [initial_eval]
  · rw [hensel_slope_initial_derivative]
    exact rational_bezout_specialized_root_smooth p A B _ C D z a certificate ps aspec bspec root
end NearCompression
