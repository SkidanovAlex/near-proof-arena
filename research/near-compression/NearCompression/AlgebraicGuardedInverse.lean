import NearCompression.AlgebraicResidueSpecialization

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- A unit certificate modulo an irreducible polynomial identifies the
actual quotient-field inverse with its polynomial multiplier. -/
theorem polynomial_residue_certificate_inverse (h p A B : Poly K)
    (irreducible : PolynomialIrreducible h)
    (certificate : PolynomialCoeffEq (A*h+B*p) (Poly.C 1)) :
    letI := polynomialResidueField h irreducible
    polynomialResidueClass h B=(polynomialResidueClass h p)⁻¹ := by
  letI := polynomialResidueField h irreducible
  have residue : PolynomialResidueEq h (B*p) (Poly.C 1) := by
    refine ⟨-A,?_⟩
    have cert:=(formal_polynomial_eq_iff _ _).mpr certificate
    change formalPolynomial A*formalPolynomial h+formalPolynomial B*formalPolynomial p=1 at cert
    apply (formal_polynomial_eq_iff _ _).mp
    change formalPolynomial B*formalPolynomial p-1= -formalPolynomial A*formalPolynomial h
    grind
  have product:= (polynomial_residue_class_eq_iff h (B*p) (Poly.C 1)).mpr residue
  change polynomialResidueClass h B*polynomialResidueClass h p=1 at product
  have nonzero : polynomialResidueClass h p≠0 := by
    intro zero
    rw [zero] at product
    have impossible : (0 : PolynomialResidue h)=1 := by grind
    exact Field.zero_ne_one impossible
  have inverse:=Field.mul_inv_cancel nonzero
  grind

/-- Safe specialization of a modular unit certificate supplies the inverse's
regular representative and its numeric inverse value. No inference from
nonzeroness at a single specialized root alone is made. -/
theorem algebraic_certificate_inverse_specializes
    (h p A B : Poly (PolynomialRational K)) (irreducible : PolynomialIrreducible h)
    (hs As Bs : Poly K) (z a value : K)
    (certificate : PolynomialCoeffEq (A*h+B*p) (Poly.C 1))
    (hsp : RationalPolynomialSpecializes h hs z)
    (asp : RationalPolynomialSpecializes A As z) (bsp : RationalPolynomialSpecializes B Bs z)
    (pvalue : PolynomialRationalValueAt (p.eval (polynomialRationalCoefficientMap.toFun a)) z value)
    (root : hs.eval a=0) :
    letI := polynomialResidueField h irreducible
    value≠0 ∧ AlgebraicResidueValueAt h ((polynomialResidueClass h p)⁻¹) z a value⁻¹ := by
  letI := polynomialResidueField h irreducible
  have identity:=synthetic_jet_congr _ _ certificate (polynomialRationalCoefficientMap.toFun a) 0
  change (A*h+B*p).eval _=(Poly.C 1).eval _ at identity
  rw [Poly.eval_add,Poly.eval_mul,Poly.eval_mul,Poly.eval_C] at identity
  have evaluated:=polynomial_rational_value_add _ _ z _ _
    (polynomial_rational_value_mul _ _ z _ _ (rational_polynomial_eval_specializes A As z a asp)
      (rational_polynomial_eval_specializes h hs z a hsp))
    (polynomial_rational_value_mul _ _ z _ _ (rational_polynomial_eval_specializes B Bs z a bsp) pvalue)
  rw [identity] at evaluated
  have numeric:=polynomial_rational_value_unique _ z _ _ evaluated (rational_coefficient_specializes 1 z)
  rw [root] at numeric
  have product : Bs.eval a*value=1 := by grind
  have nonzero : value≠0 := by
    intro zero
    rw [zero] at product
    have impossible : (0:K)=1 := by grind
    exact Field.zero_ne_one impossible
  refine ⟨nonzero,B,Bs,polynomial_residue_certificate_inverse h p A B irreducible certificate,bsp,?_⟩
  have inverse:=Field.mul_inv_cancel nonzero
  grind

/-- The source-degree-controlled derivative guard protects the actual inverse
of the algebraic modulus derivative, which is the slope inverse used in lifting. -/
theorem algebraic_derivative_guarded_inverse
    (characteristic : Nat) [IsCharP K characteristic]
    (ps : Nat→Poly K) (h : Poly (PolynomialRational K)) (d : Nat)
    (pc : ∀ i,polynomialRationalOfPolynomial (ps i)=h.coeff i)
    (irreducible : PolynomialIrreducible h) (degree : h.DegLt (d+1))
    (leading : h.coeff d≠0) (positive : 0<d) (small : d<characteristic)
    (hs : Poly K) (z a : K) (hsp : RationalPolynomialSpecializes h hs z)
    (safe : (derivativeSharedDenominator ps d).eval z≠0) (root : hs.eval a=0) :
    letI := polynomialResidueField h irreducible
    (polynomialDerivative hs).eval a≠0 ∧
      AlgebraicResidueValueAt h ((polynomialResidueClass h (polynomialDerivative h))⁻¹)
        z a ((polynomialDerivative hs).eval a)⁻¹ := by
  obtain ⟨A,B,C,D,certificate,cs,ds⟩:=irreducible_derivative_certificate_specializes
    characteristic ps h d pc irreducible degree leading positive small z safe
  exact algebraic_certificate_inverse_specializes h (polynomialDerivative h) A B irreducible
    hs C D z a _ certificate hsp cs ds (rational_polynomial_derivative_specializes h hs z a hsp) root
end NearCompression
