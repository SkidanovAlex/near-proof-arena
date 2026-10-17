import NearCompression.BivariateCurveDivision
import NearCompression.PolynomialCoefficientAlgebra
import NearCompression.PolynomialIntegralDomain

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem product_zero (p : Poly K) (i : Nat) : (p*Poly.zero).coeff i=0 :=
  (polynomial_product_zero_iff p Poly.zero).mpr (Or.inr (by intro j;rfl)) i

private theorem mul_sub (p q r : Poly K) : PolynomialCoeffEq (p*(q-r)) (p*q-p*r) := by
  intro i
  rw [polynomial_mul_comm p (q-r),polynomial_sub_mul,Poly.coeff_sub,Poly.coeff_sub,
    polynomial_mul_comm q p,polynomial_mul_comm r p]

private theorem swap (p q r : Poly K) : PolynomialCoeffEq (p*(q*r)) (q*(p*r)) := by
  intro i
  rw [←polynomial_mul_assoc,←polynomial_mul_assoc]
  exact polynomial_mul_congr (p*q) (q*p) r r (polynomial_mul_comm p q) (fun _=>rfl) i

private theorem quotient_cons (a b : Poly K) (rest : List (Poly K)) (curve : Poly K) :
    bivariateCurveQuotient (a::b::rest) curve=
      bivariateSubstitute (b::rest) curve::bivariateCurveQuotient (b::rest) curve := by
  simp [bivariateCurveQuotient,List.range_succ_eq_map,List.map_map,Function.comp_def]

/-- Formal divided-difference identity for the explicit curve quotient.
This is coefficient equality, without an evaluation-domain assumption. -/
theorem bivariate_curve_substitution_difference (rows : List (Poly K)) (f g : Poly K) :
    PolynomialCoeffEq (bivariateSubstitute rows g-bivariateSubstitute rows f)
      ((g-f)*bivariateSubstitute (bivariateCurveQuotient rows f) g) := by
  induction rows with
  | nil =>
    intro i
    change ((Poly.zero : Poly K)-Poly.zero).coeff i=((g-f)*Poly.zero).coeff i
    rw [Poly.coeff_sub,product_zero];grind
  | cons a rest ih =>
    cases rest with
    | nil =>
      intro i
      change ((a+g*Poly.zero)-(a+f*Poly.zero)).coeff i=((g-f)*Poly.zero).coeff i
      rw [Poly.coeff_sub,Poly.coeff_add,Poly.coeff_add,product_zero,product_zero,product_zero]
      grind
    | cons b rest =>
      intro i
      rw [quotient_cons]
      simp only [bivariateSubstitute] at ih ⊢
      let A:=bivariateSubstitute (b::rest) g
      let B:=bivariateSubstitute (b::rest) f
      let H:=bivariateSubstitute (bivariateCurveQuotient (b::rest) f) g
      have transported:=polynomial_mul_congr g g (A-B) ((g-f)*H) (fun _=>rfl) ih i
      rw [mul_sub,Poly.coeff_sub,swap] at transported
      change ((a+g*A)-(a+f*B)).coeff i=((g-f)*(B+g*H)).coeff i
      rw [Poly.coeff_sub,Poly.coeff_add,Poly.coeff_add,polynomial_mul_add,Poly.coeff_add,
        polynomial_sub_mul,Poly.coeff_sub]
      grind

/-- Removing one curve factor preserves every formally distinct curve root.
Distinctness is coefficientwise, so different zero padding is not enough. -/
theorem bivariate_curve_quotient_preserves_root (rows : List (Poly K)) (f g : Poly K)
    (rootF : (bivariateSubstitute rows f).IsZero)
    (rootG : (bivariateSubstitute rows g).IsZero)
    (different : ¬PolynomialCoeffEq g f) :
    (bivariateSubstitute (bivariateCurveQuotient rows f) g).IsZero := by
  have product : ((g-f)*bivariateSubstitute (bivariateCurveQuotient rows f) g).IsZero := by
    intro i
    rw [←bivariate_curve_substitution_difference rows f g,Poly.coeff_sub,rootG i,rootF i]
    grind
  rcases (polynomial_product_zero_iff _ _).mp product with equal|root
  · apply False.elim
    apply different
    intro i
    have h:=equal i
    rw [Poly.coeff_sub] at h
    grind
  · exact root
/-- A nonzero Y-polynomial has at most its stored Y-degree many pairwise
formally distinct polynomial curves as roots. No bound on field size is used. -/
theorem bivariate_curve_root_count (curves : List (Poly K))
    (distinct : curves.Pairwise (fun f g=>¬PolynomialCoeffEq g f))
    (rows : List (Poly K))
    (nonzero : ∃ i j,(rows.getD j Poly.zero).coeff i≠0)
    (roots : ∀ f∈curves,(bivariateSubstitute rows f).IsZero) :
    curves.length≤rows.length-1 := by
  induction curves generalizing rows with
  | nil => simp
  | cons f rest ih =>
    have pair:=List.pairwise_cons.mp distinct
    have rootF:=roots f (by simp)
    have qnz:=bivariate_curve_quotient_nonzero rows f nonzero rootF
    have tailRoots : ∀ g∈rest,(bivariateSubstitute (bivariateCurveQuotient rows f) g).IsZero := by
      intro g hg
      exact bivariate_curve_quotient_preserves_root rows f g rootF
        (roots g (by simp [hg])) (pair.1 g hg)
    have bound:=ih pair.2 (bivariateCurveQuotient rows f) qnz tailRoots
    have qlength:=bivariate_curve_quotient_length rows f
    have positive : 0<(bivariateCurveQuotient rows f).length := by
      obtain ⟨i,j,entry⟩:=qnz
      cases h : bivariateCurveQuotient rows f with
      | nil => simp only [h,List.getD_nil] at entry;exact False.elim (entry rfl)
      | cons a rest => simp
    simp only [List.length_cons]
    omega
end NearCompression
