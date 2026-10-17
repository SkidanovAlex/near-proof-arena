import NearCompression.SquarefreeFactorCertificates

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K L : Type} [Field K] [Field L]

/-- Coefficientwise identities survive an explicit coefficient-field map. -/
theorem transport_polynomial_coeff_congr (f : PolynomialFieldMap K L) (p q : Poly K)
    (same : PolynomialCoeffEq p q) :
    PolynomialCoeffEq (transportPolynomial f p) (transportPolynomial f q) := by
  intro i
  rw [transport_polynomial_coefficient,transport_polynomial_coefficient,same]

/-- A separable nonconstant source supplies an actual irreducible selected
factor, complement, inherited Y-degree bounds and both unit certificates.
This does not bound parameter degrees of rational-function representatives. -/
theorem separable_factor_selection (p S T : Poly K) (D : Nat)
    (nonzero : ¬p.IsZero) (nonconstant : ¬p.DegLt 1) (degree : p.DegLt D)
    (certificate : PolynomialCoeffEq (S*p+T*polynomialDerivative p) (Poly.C 1)) :
    ∃ h g U V W : Poly K, PolynomialIrreducible h ∧
      PolynomialCoeffEq p (h*g) ∧ h.DegLt D ∧ g.DegLt D ∧
      PolynomialCoeffEq (U*h+V*g) (Poly.C 1) ∧
      PolynomialCoeffEq (U*h+W*polynomialDerivative h) (Poly.C 1) := by
  obtain ⟨h,irreducible,g,fac⟩:=polynomial_irreducible_divisor_exists p nonzero nonconstant
  have factorization : PolynomialCoeffEq p (h*g) := fun i=>(fac i).trans (polynomial_mul_comm g h i)
  refine ⟨h,g,S*g+T*polynomialDerivative g,T*polynomialDerivative h,T*g,
    irreducible,factorization,?_,?_,?_,?_⟩
  · exact polynomial_divisor_degree p h D nonzero degree ⟨g,fac⟩
  · exact polynomial_divisor_degree p g D nonzero degree ⟨h,factorization⟩
  · exact squarefree_factor_complement_certificate p h g S T factorization certificate
  · exact squarefree_selected_factor_certificate p h g S T factorization certificate

/-- A selected irreducible factor gives a concrete root in the constructed
quotient field. The source derivative certificate proves that the source root
is smooth, and that its complementary factor is nonzero at that root. -/
theorem selected_factor_extension_root (p h g S T : Poly K)
    (irreducible : PolynomialIrreducible h)
    (factorization : PolynomialCoeffEq p (h*g))
    (certificate : PolynomialCoeffEq (S*p+T*polynomialDerivative p) (Poly.C 1)) :
    letI := polynomialResidueField h irreducible
    let f := polynomialResidueEmbedding h irreducible
    let a := polynomialResidueClass h Poly.X
    (transportPolynomial f p).eval a=0 ∧
      (polynomialDerivative (transportPolynomial f p)).eval a≠0 ∧
      (transportPolynomial f g).eval a≠0 := by
  letI := polynomialResidueField h irreducible
  let f := polynomialResidueEmbedding h irreducible
  let a := polynomialResidueClass h Poly.X
  change (transportPolynomial f p).eval a=0 ∧
    (polynomialDerivative (transportPolynomial f p)).eval a≠0 ∧
    (transportPolynomial f g).eval a≠0
  have root : (transportPolynomial f h).eval a=0 := polynomial_residue_modulus_root h irreducible
  have fac:=transport_polynomial_coeff_congr f p (h*g) factorization
  rw [transport_polynomial_mul] at fac
  have cert:=transport_polynomial_bezout f p (polynomialDerivative p) S T certificate
  rw [transport_polynomial_derivative] at cert
  have conditions:=squarefree_selected_root_conditions (transportPolynomial f p)
    (transportPolynomial f h) (transportPolynomial f g) (transportPolynomial f S)
    (transportPolynomial f T) a fac cert root
  have source:=selected_factor_initial_smooth _ _ _ a fac root conditions.1 conditions.2
  exact ⟨source.1,source.2,conditions.2⟩

/-- Existence, degree inheritance, source-root smoothness and complementary
nonvanishing are now composed in one constructed-extension statement. -/
theorem separable_source_smooth_extension_exists (p S T : Poly K) (D : Nat)
    (nonzero : ¬p.IsZero) (nonconstant : ¬p.DegLt 1) (degree : p.DegLt D)
    (certificate : PolynomialCoeffEq (S*p+T*polynomialDerivative p) (Poly.C 1)) :
    ∃ h g : Poly K, ∃ irreducible : PolynomialIrreducible h,
      PolynomialCoeffEq p (h*g) ∧ h.DegLt D ∧ g.DegLt D ∧
      (letI := polynomialResidueField h irreducible
       let f := polynomialResidueEmbedding h irreducible
       let a := polynomialResidueClass h Poly.X
       (transportPolynomial f p).eval a=0 ∧
         (polynomialDerivative (transportPolynomial f p)).eval a≠0 ∧
         (transportPolynomial f g).eval a≠0) := by
  obtain ⟨h,g,U,V,W,irreducible,fac,hd,gd,_,_⟩:=separable_factor_selection p S T D nonzero nonconstant degree certificate
  exact ⟨h,g,irreducible,fac,hd,gd,selected_factor_extension_root p h g S T irreducible fac certificate⟩
/-- Taking the X=0 initial polynomial commutes with coefficient-field extension. -/
theorem initial_polynomial_field_transport (f : PolynomialFieldMap K L) (rows : List (Poly K)) :
    initialYPolynomial (rows.map (transportPolynomial f))=transportPolynomial f (initialYPolynomial rows) := by
  unfold initialYPolynomial transportPolynomial
  simp only [List.map_map,Function.comp_def]
  congr 2
  funext p
  exact transport_polynomial_coefficient f p 0

private theorem initial_eval (rows : List (Poly K)) (a : K) :
    (bivariateSubstitute rows (Poly.C a)).coeff 0=(initialYPolynomial rows).eval a := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [bivariateSubstitute,Poly.coeff_add]
    rw [polynomial_order_product_coefficient (Poly.C a) (bivariateSubstitute rows (Poly.C a)) 0 0
      (by intro i hi;omega) (by intro i hi;omega)]
    change row.coeff 0+a*(bivariateSubstitute rows (Poly.C a)).coeff 0=
      row.coeff 0+a*(initialYPolynomial rows).eval a
    rw [ih]

/-- A nonconstant separable initial polynomial constructs an algebraic root
and finite Hensel lifts in its quotient field at every requested precision.
No polynomial initial branch over the original field is assumed. -/
theorem separable_initial_extension_hensel_exists (rows : List (Poly K)) (S T : Poly K) (D : Nat)
    (nonzero : ¬(initialYPolynomial rows).IsZero)
    (nonconstant : ¬(initialYPolynomial rows).DegLt 1)
    (degree : (initialYPolynomial rows).DegLt D)
    (certificate : PolynomialCoeffEq
      (S*initialYPolynomial rows+T*polynomialDerivative (initialYPolynomial rows)) (Poly.C 1)) :
    ∃ h : Poly K, ∃ irreducible : PolynomialIrreducible h, h.DegLt D ∧
      (letI := polynomialResidueField h irreducible
       let extended := rows.map (transportPolynomial (polynomialResidueEmbedding h irreducible))
       let a := polynomialResidueClass h Poly.X
       ∀ n : Nat, (curveHenselLift extended a n).coeff 0=a ∧
         (curveHenselLift extended a n).DegLt (n+1) ∧
         PolynomialOrder (bivariateSubstitute extended (curveHenselLift extended a n)) (n+1)) := by
  obtain ⟨h,g,irreducible,_,hd,_,conditions⟩:=separable_source_smooth_extension_exists
    (initialYPolynomial rows) S T D nonzero nonconstant degree certificate
  refine ⟨h,irreducible,hd,?_⟩
  letI := polynomialResidueField h irreducible
  let f := polynomialResidueEmbedding h irreducible
  let a := polynomialResidueClass h Poly.X
  dsimp only
  intro n
  apply hensel_finite_lift (rows.map (transportPolynomial f)) a _ _ n
  · rw [initial_eval,initial_polynomial_field_transport]
    exact conditions.1
  · rw [hensel_slope_initial_derivative,initial_polynomial_field_transport]
    exact conditions.2.1
end NearCompression
