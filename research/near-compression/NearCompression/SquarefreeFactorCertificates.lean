import NearCompression.FactorCollisionGuard

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- The formal derivative product rule is recovered at a transcendental
indeterminate. Agreement on the finite base field is never used. -/
theorem polynomial_derivative_mul (p q : Poly K) :
    PolynomialCoeffEq (polynomialDerivative (p*q))
      (polynomialDerivative p*q+p*polynomialDerivative q) := by
  apply (polynomial_rational_of_polynomial_eq_iff _ _).mp
  rw [←polynomial_rational_eval_variable (polynomialDerivative (p*q)),
    ←polynomial_rational_eval_variable (polynomialDerivative p*q+p*polynomialDerivative q)]
  rw [transport_polynomial_derivative,transport_polynomial_mul,transport_polynomial_add,
    transport_polynomial_mul,transport_polynomial_mul,transport_polynomial_derivative,
    transport_polynomial_derivative,Poly.eval_add,Poly.eval_mul,Poly.eval_mul]
  exact polynomial_derivative_product_eval _ _ _

/-- Derivatives respect coefficient equality, independently of list padding. -/
theorem polynomial_derivative_coeff_congr (p q : Poly K) (same : PolynomialCoeffEq p q) :
    PolynomialCoeffEq (polynomialDerivative p) (polynomialDerivative q) := by
  intro i
  rw [polynomial_derivative_coefficient,polynomial_derivative_coefficient,same]

/-- A derivative unit certificate for the source constructs an explicit unit
certificate between any selected factor and its complement. -/
theorem squarefree_factor_complement_certificate (p h g S T : Poly K)
    (factorization : PolynomialCoeffEq p (h*g))
    (certificate : PolynomialCoeffEq (S*p+T*polynomialDerivative p) (Poly.C 1)) :
    PolynomialCoeffEq
      ((S*g+T*polynomialDerivative g)*h+(T*polynomialDerivative h)*g) (Poly.C 1) := by
  have fac:=(formal_polynomial_eq_iff _ _).mpr factorization
  have der:=(formal_polynomial_eq_iff _ _).mpr
    (fun i=>(polynomial_derivative_coeff_congr p (h*g) factorization i).trans (polynomial_derivative_mul h g i))
  have cert:=(formal_polynomial_eq_iff _ _).mpr certificate
  change formalPolynomial p=formalPolynomial h*formalPolynomial g at fac
  change formalPolynomial (polynomialDerivative p)=
    formalPolynomial (polynomialDerivative h)*formalPolynomial g+formalPolynomial h*formalPolynomial (polynomialDerivative g) at der
  change formalPolynomial S*formalPolynomial p+formalPolynomial T*formalPolynomial (polynomialDerivative p)=1 at cert
  apply (formal_polynomial_eq_iff _ _).mp
  change (formalPolynomial S*formalPolynomial g+formalPolynomial T*formalPolynomial (polynomialDerivative g))*formalPolynomial h+
    (formalPolynomial T*formalPolynomial (polynomialDerivative h))*formalPolynomial g=1
  grind

/-- The same source certificate also proves every selected factor separable,
with explicit multipliers rather than an assumed squarefree inheritance law. -/
theorem squarefree_selected_factor_certificate (p h g S T : Poly K)
    (factorization : PolynomialCoeffEq p (h*g))
    (certificate : PolynomialCoeffEq (S*p+T*polynomialDerivative p) (Poly.C 1)) :
    PolynomialCoeffEq
      ((S*g+T*polynomialDerivative g)*h+(T*g)*polynomialDerivative h) (Poly.C 1) := by
  have complement:=(formal_polynomial_eq_iff _ _).mpr
    (squarefree_factor_complement_certificate p h g S T factorization certificate)
  apply (formal_polynomial_eq_iff _ _).mp
  change (formalPolynomial S*formalPolynomial g+formalPolynomial T*formalPolynomial (polynomialDerivative g))*formalPolynomial h+
    (formalPolynomial T*formalPolynomial g)*formalPolynomial (polynomialDerivative h)=1
  change (formalPolynomial S*formalPolynomial g+formalPolynomial T*formalPolynomial (polynomialDerivative g))*formalPolynomial h+
    (formalPolynomial T*formalPolynomial (polynomialDerivative h))*formalPolynomial g=1 at complement
  grind

/-- A selected factor's root is smooth and cannot be a complementary root
when the entire source has a derivative unit certificate. -/
theorem squarefree_selected_root_conditions (p h g S T : Poly K) (a : K)
    (factorization : PolynomialCoeffEq p (h*g))
    (certificate : PolynomialCoeffEq (S*p+T*polynomialDerivative p) (Poly.C 1))
    (root : h.eval a=0) : (polynomialDerivative h).eval a≠0 ∧ g.eval a≠0 := by
  constructor
  · exact bezout_no_common_root h (polynomialDerivative h) _ _ 1 a
      (squarefree_selected_factor_certificate p h g S T factorization certificate)
      (fun zero=>Field.zero_ne_one zero.symm) root
  · exact bezout_no_common_root h g _ _ 1 a
      (squarefree_factor_complement_certificate p h g S T factorization certificate)
      (fun zero=>Field.zero_ne_one zero.symm) root
/-- The factor-collision budget now follows from a derivative certificate for
the entire source; a separate factor/complement certificate is unnecessary. -/
theorem squarefree_parameter_factor_collision_count
    (source S T : Poly (PolynomialRational K)) (hs gs : List (Poly K)) (m n D : Nat)
    (factorization : PolynomialCoeffEq source (polynomialParameterFamily hs*polynomialParameterFamily gs))
    (certificate : PolynomialCoeffEq (S*source+T*polynomialDerivative source) (Poly.C 1))
    (positive : 0<m) (hd : (polynomialParameterFamily hs).DegLt (m+1))
    (gd : (polynomialParameterFamily gs).DegLt (n+1))
    (gl : (polynomialParameterFamily gs).coeff n≠0)
    (hsd : ∀ i,(hs.getD i Poly.zero).DegLt (D+1))
    (gsd : ∀ i,(gs.getD i Poly.zero).DegLt (D+1))
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun z=>∃ a : K,(polynomialParameterSpecialize hs z).eval a=0 ∧
      (polynomialParameterSpecialize gs z).eval a=0)≤(n+m)*D := by
  exact parameter_factor_collision_count hs gs _ _ m n D positive hd gd gl
    (squarefree_factor_complement_certificate source _ _ S T factorization certificate)
    hsd gsd sample distinct
end NearCompression
