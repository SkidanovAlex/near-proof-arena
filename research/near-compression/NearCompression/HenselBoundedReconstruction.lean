import NearCompression.HenselCoefficientStep

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem constant_congr (rows : List (Poly K)) (f g : Poly K)
    (same : f.coeff 0=g.coeff 0) :
    (bivariateSubstitute rows f).coeff 0=(bivariateSubstitute rows g).coeff 0 := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have product (p q : Poly K) : (p*q).coeff 0=p.coeff 0*q.coeff 0 :=
      polynomial_order_product_coefficient p q 0 0 (by intro i hi;omega) (by intro i hi;omega)
    simp only [bivariateSubstitute,Poly.coeff_add,product,same,ih]

private theorem substitution_congr (rows : List (Poly K)) (f g : Poly K)
    (same : PolynomialCoeffEq f g) :
    PolynomialCoeffEq (bivariateSubstitute rows f) (bivariateSubstitute rows g) := by
  induction rows with
  | nil => intro i;rfl
  | cons row rest ih =>
    intro i
    simp only [bivariateSubstitute,Poly.coeff_add]
    rw [polynomial_mul_congr f g _ _ same ih i]

/-- A bounded-degree smooth exact root is recovered coefficientwise by the
finite lift. This is a completeness theorem, not an assumption of termination. -/
theorem hensel_reconstruct_bounded_root (rows : List (Poly K)) (f : Poly K) (n : Nat)
    (degree : f.DegLt (n+1)) (root : (bivariateSubstitute rows f).IsZero)
    (smooth : curveHenselSlope rows f≠0) :
    PolynomialCoeffEq (curveHenselLift rows (f.coeff 0) n) f := by
  let a:=f.coeff 0
  have same : (Poly.C a).coeff 0=f.coeff 0 := rfl
  have initial : (bivariateSubstitute rows (Poly.C a)).coeff 0=0 :=
    (constant_congr rows (Poly.C a) f same).trans (root 0)
  have nonsingular : curveHenselSlope rows (Poly.C a)≠0 := by
    rw [hensel_slope_constant_congr rows (Poly.C a) f same]
    exact smooth
  have lift:=hensel_finite_lift rows a initial nonsingular n
  have equalConstant : f.coeff 0=(curveHenselLift rows a n).coeff 0 := lift.1.symm
  have equalLow:=hensel_lift_unique_modulo rows f (curveHenselLift rows a n)
    equalConstant smooth (n+1) (fun i _=>root i) lift.2.2
  intro i
  by_cases low : i<n+1
  · have h:=equalLow i low
    rw [Poly.coeff_sub] at h
    grind
  · have bound : n+1≤i := by omega
    rw [lift.2.1 i bound,degree i bound]

/-- Exact residual checking after k corrections is sound and complete for
roots of degree≤k through a given smooth initial value. -/
theorem hensel_bounded_root_iff (rows : List (Poly K)) (a : K) (k : Nat)
    (initial : (bivariateSubstitute rows (Poly.C a)).coeff 0=0)
    (smooth : curveHenselSlope rows (Poly.C a)≠0) :
    (∃ f : Poly K,f.coeff 0=a ∧ f.DegLt (k+1) ∧ (bivariateSubstitute rows f).IsZero) ↔
      (bivariateSubstitute rows (curveHenselLift rows a k)).IsZero := by
  constructor
  · rintro ⟨f,constant,degree,root⟩
    have same : f.coeff 0=(Poly.C a).coeff 0 := constant
    have ns : curveHenselSlope rows f≠0 := by
      rw [hensel_slope_constant_congr rows f (Poly.C a) same]
      exact smooth
    have equal:=hensel_reconstruct_bounded_root rows f k degree root ns
    rw [constant] at equal
    intro i
    rw [substitution_congr rows _ f equal i]
    exact root i
  · intro root
    have lift:=hensel_finite_lift rows a initial smooth k
    exact ⟨curveHenselLift rows a k,lift.1,lift.2.1,root⟩

/-- A finite lift is exact once its residual precision covers the weighted
substitution bound and its high curve coefficients vanish. The latter is an
explicit, checkable premise, not inferred from smoothness alone. -/
theorem hensel_bounded_tail_exact (rows : List (Poly K)) (a : K) (k D n : Nat)
    (initial : (bivariateSubstitute rows (Poly.C a)).coeff 0=0)
    (smooth : curveHenselSlope rows (Poly.C a)≠0)
    (weighted : BivariateWeightedDegree rows k D) (precision : D≤n+1)
    (tail : (curveHenselLift rows a n).DegLt (k+1)) :
    (bivariateSubstitute rows (curveHenselLift rows a n)).IsZero := by
  have lift:=hensel_finite_lift rows a initial smooth n
  have degree:=bivariate_substitution_degree rows (curveHenselLift rows a n) k D tail weighted
  intro i
  by_cases low : i<n+1
  · exact lift.2.2 i low
  · exact degree i (by omega)

/-- With enough precision, vanishing high coefficients of the smooth lift
is equivalent to existence of a bounded-degree exact root with that constant. -/
theorem hensel_bounded_tail_iff (rows : List (Poly K)) (a : K) (k D n : Nat)
    (initial : (bivariateSubstitute rows (Poly.C a)).coeff 0=0)
    (smooth : curveHenselSlope rows (Poly.C a)≠0)
    (weighted : BivariateWeightedDegree rows k D) (precision : D≤n+1) (enough : k≤n) :
    (curveHenselLift rows a n).DegLt (k+1) ↔
      ∃ f : Poly K,f.coeff 0=a ∧ f.DegLt (k+1) ∧ (bivariateSubstitute rows f).IsZero := by
  constructor
  · intro tail
    have lift:=hensel_finite_lift rows a initial smooth n
    exact ⟨curveHenselLift rows a n,lift.1,tail,
      hensel_bounded_tail_exact rows a k D n initial smooth weighted precision tail⟩
  · rintro ⟨f,constant,degree,root⟩
    have same : f.coeff 0=(Poly.C a).coeff 0 := constant
    have ns : curveHenselSlope rows f≠0 := by
      rw [hensel_slope_constant_congr rows f (Poly.C a) same]
      exact smooth
    have equal:=hensel_reconstruct_bounded_root rows f n (Poly.DegLt.mono degree (by omega)) root ns
    rw [constant] at equal
    intro i hi
    rw [equal i]
    exact degree i hi
end NearCompression
