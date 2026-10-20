import NearCompression.PolynomialParameterFamily

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem product_zero (p q : Poly K) : (p*q).coeff 0=p.coeff 0*q.coeff 0 :=
  polynomial_order_product_coefficient p q 0 0 (by intro i hi;omega) (by intro i hi;omega)

private theorem product_one (p q : Poly K) :
    (p*q).coeff 1=p.coeff 0*q.coeff 1+p.coeff 1*q.coeff 0 := by
  cases p with | mk ps => cases ps with
    | nil => change (0:K)=0*q.coeff 1+0*q.coeff 0;grind
    | cons c cs =>
      change (Poly.smul c q+Poly.mk (0::Poly.mulL cs q.coeffs)).coeff 1=_
      rw [Poly.coeff_add,Poly.coeff_smul]
      change c*q.coeff 1+((Poly.mk cs)*q).coeff 0=c*q.coeff 1+(Poly.mk cs).coeff 0*q.coeff 0
      rw [product_zero]

/-- Formal derivative product rule at a point, derived from multiplicative
formal translation. It remains valid in small characteristic. -/
theorem polynomial_derivative_product_eval (p q : Poly K) (a : K) :
    (polynomialDerivative (p*q)).eval a=
      (polynomialDerivative p).eval a*q.eval a+p.eval a*(polynomialDerivative q).eval a := by
  have entry:=polynomial_translate_mul p q a 1
  rw [product_one,polynomial_translate_coeff,polynomial_translate_coeff,
    polynomial_translate_coeff,polynomial_translate_coeff,polynomial_translate_coeff] at entry
  change ((p*q).quot a).eval a=p.eval a*(q.quot a).eval a+(p.quot a).eval a*q.eval a at entry
  rw [polynomial_derivative_eval_quotient,polynomial_derivative_eval_quotient,
    polynomial_derivative_eval_quotient]
  grind

/-- At a selected factor's root, product smoothness is equivalent to smoothness
of that factor and noncollision with the complementary factor. -/
theorem selected_factor_smooth_iff (h g : Poly K) (a : K) (root : h.eval a=0) :
    (polynomialDerivative (h*g)).eval a≠0 ↔
      (polynomialDerivative h).eval a≠0 ∧ g.eval a≠0 := by
  rw [polynomial_derivative_product_eval,root]
  constructor
  · intro smooth
    constructor
    · intro zero;apply smooth;rw [zero];grind
    · intro zero;apply smooth;rw [zero];grind
  · intro good zero
    have product : (polynomialDerivative h).eval a*g.eval a=0 := by grind
    rcases Field.of_mul_eq_zero product with left|right
    · exact good.1 left
    · exact good.2 right

/-- Repeated selected factors cannot support a simple-root Hensel lift. -/
theorem repeated_factor_root_singular (h g : Poly K) (a : K) (root : h.eval a=0) :
    (polynomialDerivative (h*(h*g))).eval a=0 := by
  rw [polynomial_derivative_product_eval,Poly.eval_mul,root]
  grind

private theorem equal_eval (p q : Poly K) (same : PolynomialCoeffEq p q) (a : K) : p.eval a=q.eval a :=
  synthetic_jet_congr p q same a 0

private theorem equal_derivative_eval (p q : Poly K) (same : PolynomialCoeffEq p q) (a : K) :
    (polynomialDerivative p).eval a=(polynomialDerivative q).eval a := by
  rw [polynomial_derivative_eval_quotient,polynomial_derivative_eval_quotient]
  exact synthetic_jet_congr p q same a 1

/-- A coefficientwise factorization transfers the selected factor criterion
to the actual initial polynomial, regardless of coefficient-list padding. -/
theorem selected_factor_initial_smooth (p h g : Poly K) (a : K)
    (factorization : PolynomialCoeffEq p (h*g)) (root : h.eval a=0)
    (smooth : (polynomialDerivative h).eval a≠0) (noncollision : g.eval a≠0) :
    p.eval a=0 ∧ (polynomialDerivative p).eval a≠0 := by
  constructor
  · rw [equal_eval p (h*g) factorization a,Poly.eval_mul,root];grind
  · rw [equal_derivative_eval p (h*g) factorization a]
    exact (selected_factor_smooth_iff h g a root).mpr ⟨smooth,noncollision⟩

/-- An explicit unit certificate against the complementary factor discharges
the noncollision condition at every root of the selected factor. -/
theorem selected_factor_coprime_smooth (p h g A B : Poly K) (a : K)
    (factorization : PolynomialCoeffEq p (h*g)) (root : h.eval a=0)
    (smooth : (polynomialDerivative h).eval a≠0)
    (certificate : PolynomialCoeffEq (A*h+B*g) (Poly.C 1)) :
    p.eval a=0 ∧ (polynomialDerivative p).eval a≠0 := by
  exact selected_factor_initial_smooth p h g a factorization root smooth
    (bezout_no_common_root h g A B 1 a certificate (fun zero=>Field.zero_ne_one zero.symm) root)

private theorem initial_eval (rows : List (Poly K)) (a : K) :
    (bivariateSubstitute rows (Poly.C a)).coeff 0=(initialYPolynomial rows).eval a := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [bivariateSubstitute,Poly.coeff_add,product_zero]
    change row.coeff 0+a*(bivariateSubstitute rows (Poly.C a)).coeff 0=
      row.coeff 0+a*(initialYPolynomial rows).eval a
    rw [ih]

/-- Lifting the actual source requires only a smooth selected factor and
noncollision, not irreducibility of the entire initial polynomial. -/
theorem selected_factor_hensel_lift (rows : List (Poly K)) (h g : Poly K) (a : K) (n : Nat)
    (factorization : PolynomialCoeffEq (initialYPolynomial rows) (h*g))
    (root : h.eval a=0) (smooth : (polynomialDerivative h).eval a≠0) (noncollision : g.eval a≠0) :
    (curveHenselLift rows a n).coeff 0=a ∧ (curveHenselLift rows a n).DegLt (n+1) ∧
    PolynomialOrder (bivariateSubstitute rows (curveHenselLift rows a n)) (n+1) := by
  have conditions:=selected_factor_initial_smooth _ h g a factorization root smooth noncollision
  apply hensel_finite_lift rows a _ _ n
  · rw [initial_eval];exact conditions.1
  · rw [hensel_slope_initial_derivative];exact conditions.2
end NearCompression
