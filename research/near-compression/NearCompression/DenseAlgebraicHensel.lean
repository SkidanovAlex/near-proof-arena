import NearCompression.PartialHenselSpecialization

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Rational coefficients embed as constant algebraic representatives. -/
theorem algebraic_residue_rational_constant (h : Poly (PolynomialRational K))
    (r : PolynomialRational K) (z a value : K) (safe : PolynomialRationalValueAt r z value) :
    AlgebraicResidueValueAt h (polynomialResidueClass h (Poly.C r)) z a value := by
  exact ⟨Poly.C r,Poly.C value,rfl,.cons safe .nil,Poly.eval_C value a⟩

/-- The residue indeterminate specializes to the chosen numeric root value. -/
theorem algebraic_residue_variable_value (h : Poly (PolynomialRational K)) (z a : K) :
    AlgebraicResidueValueAt h (polynomialResidueClass h Poly.X) z a a := by
  refine ⟨Poly.X,Poly.X,rfl,?_,Poly.eval_X a⟩
  exact .cons (rational_coefficient_specializes 0 z) (.cons (rational_coefficient_specializes 1 z) .nil)

/-- Embed dense X,Y,Z data as Y rows of X polynomials over K(Z). -/
def denseTrivariateRationalRows (rows : List (List (Poly K))) : List (Poly (PolynomialRational K)) :=
  rows.map polynomialParameterFamily

/-- Initial-polynomial extraction agrees before either field extension or
parameter specialization. -/
theorem dense_rational_initial_polynomial (rows : List (List (Poly K))) :
    initialYPolynomial (denseTrivariateRationalRows rows)=
      polynomialParameterFamily (trivariateInitialRows rows) := by
  unfold initialYPolynomial denseTrivariateRationalRows polynomialParameterFamily trivariateInitialRows
  simp only [List.map_map,Function.comp_def]
  congr 2
  funext row
  exact (polynomial_parameter_family_coefficient row 0).symm

/-- All source coefficients of the actual dense algebraic input specialize
to the numeric dense input, including empty rows and padding. -/
theorem dense_algebraic_source_specializes (h : Poly (PolynomialRational K))
    (irreducible : PolynomialIrreducible h) (rows : List (List (Poly K))) (z a : K) :
    letI := polynomialResidueField h irreducible
    RelatedPolynomialRows (algebraicResiduePartialRelation h irreducible z a)
      ((denseTrivariateRationalRows rows).map (transportPolynomial (polynomialResidueEmbedding h irreducible)))
      (denseTrivariateSpecialize rows z) := by
  letI := polynomialResidueField h irreducible
  induction rows with
  | nil => exact .nil
  | cons row rows ih =>
    refine .cons ?_ ih
    intro i
    rw [transport_polynomial_coefficient]
    change AlgebraicResidueValueAt h
      (polynomialResidueClass h (Poly.C ((polynomialParameterFamily row).coeff i))) z a
      ((polynomialParameterSpecialize row z).coeff i)
    exact algebraic_residue_rational_constant h _ z a _
      (rational_polynomial_specializes_coefficient _ _ z (polynomial_parameter_family_specializes row z) i)

/-- The operational algebraic slope is the class of the derivative of the
full initial source polynomial, not necessarily the modulus derivative. -/
theorem dense_algebraic_initial_slope (h : Poly (PolynomialRational K))
    (irreducible : PolynomialIrreducible h) (rows : List (List (Poly K))) :
    letI := polynomialResidueField h irreducible
    curveHenselSlope
      ((denseTrivariateRationalRows rows).map (transportPolynomial (polynomialResidueEmbedding h irreducible)))
      (Poly.C (polynomialResidueClass h Poly.X))=
      polynomialResidueClass h (polynomialDerivative (polynomialParameterFamily (trivariateInitialRows rows))) := by
  letI := polynomialResidueField h irreducible
  rw [hensel_slope_initial_derivative,initial_polynomial_field_transport,dense_rational_initial_polynomial,
    ←transport_polynomial_derivative,polynomial_residue_eval_variable]

/-- Concrete dense source data and a safely specialized modular unit
certificate discharge every recurrence-specialization interface, including
the actual full-source slope inverse. The modulus may be a proper factor
of the initial source polynomial. -/
theorem dense_algebraic_hensel_specializes (h A B : Poly (PolynomialRational K))
    (irreducible : PolynomialIrreducible h) (rows : List (List (Poly K)))
    (hs As Bs : Poly K) (z a : K)
    (certificate : PolynomialCoeffEq
      (A*h+B*polynomialDerivative (polynomialParameterFamily (trivariateInitialRows rows))) (Poly.C 1))
    (hsp : RationalPolynomialSpecializes h hs z)
    (asp : RationalPolynomialSpecializes A As z) (bsp : RationalPolynomialSpecializes B Bs z)
    (root : hs.eval a=0) :
    letI := polynomialResidueField h irreducible
    ∀ n i,AlgebraicResidueValueAt h
      ((curveHenselLift
        ((denseTrivariateRationalRows rows).map (transportPolynomial (polynomialResidueEmbedding h irreducible)))
        (polynomialResidueClass h Poly.X) n).coeff i) z a
      ((curveHenselLift (denseTrivariateSpecialize rows z) a n).coeff i) := by
  letI := polynomialResidueField h irreducible
  have initialSpecializes : RationalPolynomialSpecializes
      (polynomialParameterFamily (trivariateInitialRows rows))
      (initialYPolynomial (denseTrivariateSpecialize rows z)) z := by
    rw [←trivariate_initial_parameter_specialization]
    exact polynomial_parameter_family_specializes _ z
  have inverse:=algebraic_certificate_inverse_specializes h
    (polynomialDerivative (polynomialParameterFamily (trivariateInitialRows rows))) A B irreducible
    hs As Bs z a _ certificate hsp asp bsp
    (rational_polynomial_derivative_specializes _ _ z a initialSpecializes) root
  intro n i
  apply algebraic_hensel_lift_specializes h irreducible z a _ _ (polynomialResidueClass h Poly.X)
    (dense_algebraic_source_specializes h irreducible rows z a)
    (algebraic_residue_variable_value h z a) _ n i
  rw [dense_algebraic_initial_slope,hensel_slope_initial_derivative]
  exact inverse.2
end NearCompression
