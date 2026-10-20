import NearCompression.FormalRootForcing

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Slope at X=0, expressed via the formal divided-difference quotient. -/
def curveHenselSlope (rows : List (Poly K)) (f : Poly K) : K :=
  (bivariateSubstitute (bivariateCurveQuotient rows f) f).coeff 0

/-- Add a single X^n coefficient; lower coefficients remain unchanged. -/
def curveHenselPerturb (f : Poly K) (n : Nat) (c : K) : Poly K :=
  f+Poly.smul c (jetMonomial n)

private theorem product_constant (p q : Poly K) : (p*q).coeff 0=p.coeff 0*q.coeff 0 :=
  polynomial_order_product_coefficient p q 0 0 (by intro i hi;omega) (by intro i hi;omega)

private theorem substitute_constant_congr (rows : List (Poly K)) (f g : Poly K)
    (same : f.coeff 0=g.coeff 0) :
    (bivariateSubstitute rows f).coeff 0=(bivariateSubstitute rows g).coeff 0 := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [bivariateSubstitute,Poly.coeff_add,product_constant,same,ih]

/-- Perturbations of order n change the residual only at order n or higher. -/
theorem hensel_perturbation_order (rows : List (Poly K)) (f g : Poly K) (n : Nat)
    (order : PolynomialOrder (g-f) n) :
    PolynomialOrder (bivariateSubstitute rows g-bivariateSubstitute rows f) n := by
  intro i hi
  rw [bivariate_curve_substitution_difference]
  exact polynomial_order_mul n 0 (g-f)
    (bivariateSubstitute (bivariateCurveQuotient rows f) g) order
    (by intro j hj;omega) i (by omega)

/-- The next residual coefficient changes linearly with the next curve
coefficient. Positivity of n fixes the constant term, hence the slope. -/
theorem hensel_perturbation_coefficient (rows : List (Poly K)) (f g : Poly K) (n : Nat)
    (positive : 0<n) (order : PolynomialOrder (g-f) n) :
    (bivariateSubstitute rows g-bivariateSubstitute rows f).coeff n=
      (g-f).coeff n*curveHenselSlope rows f := by
  have same : g.coeff 0=f.coeff 0 := by
    have h:=order 0 positive
    rw [Poly.coeff_sub] at h
    grind
  rw [bivariate_curve_substitution_difference]
  have coefficient:=polynomial_order_product_coefficient (g-f)
    (bivariateSubstitute (bivariateCurveQuotient rows f) g) n 0 order (by intro i hi;omega)
  simp only [Nat.add_zero] at coefficient
  rw [coefficient,substitute_constant_congr _ g f same]
  rfl

private theorem perturb_difference (f : Poly K) (n : Nat) (c : K) (i : Nat) :
    (curveHenselPerturb f n c-f).coeff i=if i=n then c else 0 := by
  rw [Poly.coeff_sub,curveHenselPerturb,Poly.coeff_add,Poly.coeff_smul,jet_monomial_coefficient]
  split <;> grind

private theorem perturb_order (f : Poly K) (n : Nat) (c : K) :
    PolynomialOrder (curveHenselPerturb f n c-f) n := by
  intro i hi
  rw [perturb_difference,ite_eq_right (by omega)]

private theorem perturb_coefficient (rows : List (Poly K)) (f : Poly K) (n : Nat)
    (positive : 0<n) (c : K) :
    (bivariateSubstitute rows (curveHenselPerturb f n c)).coeff n=
      (bivariateSubstitute rows f).coeff n+c*curveHenselSlope rows f := by
  have h:=hensel_perturbation_coefficient rows f (curveHenselPerturb f n c) n positive (perturb_order f n c)
  rw [Poly.coeff_sub,perturb_difference,ite_eq_left rfl] at h
  grind

/-- Construct one further Hensel coefficient from a nonsingular approximate
root. This is a finite formal lift, not rational-function factor selection. -/
theorem hensel_coefficient_step (rows : List (Poly K)) (f : Poly K) (n : Nat)
    (positive : 0<n) (residual : PolynomialOrder (bivariateSubstitute rows f) n)
    (smooth : curveHenselSlope rows f≠0) :
    PolynomialOrder (bivariateSubstitute rows
      (curveHenselPerturb f n (-(bivariateSubstitute rows f).coeff n*(curveHenselSlope rows f)⁻¹))) (n+1) := by
  let c:=-(bivariateSubstitute rows f).coeff n*(curveHenselSlope rows f)⁻¹
  intro i hi
  by_cases low : i<n
  · have h:=hensel_perturbation_order rows f (curveHenselPerturb f n c) n (perturb_order f n c) i low
    rw [Poly.coeff_sub,residual i low] at h
    change (bivariateSubstitute rows (curveHenselPerturb f n c)).coeff i=0
    grind
  · have equal : i=n := by omega
    subst i
    rw [perturb_coefficient rows f n positive]
    have inverse:=Field.mul_inv_cancel smooth
    grind

/-- The next coefficient is unique for a fixed smooth approximate root.
The nonsingularity premise cannot be omitted in positive characteristic. -/
theorem hensel_coefficient_unique (rows : List (Poly K)) (f : Poly K) (n : Nat)
    (positive : 0<n) (smooth : curveHenselSlope rows f≠0) (c d : K)
    (hc : PolynomialOrder (bivariateSubstitute rows (curveHenselPerturb f n c)) (n+1))
    (hd : PolynomialOrder (bivariateSubstitute rows (curveHenselPerturb f n d)) (n+1)) : c=d := by
  have left:=hc n (by omega)
  have right:=hd n (by omega)
  rw [perturb_coefficient rows f n positive] at left right
  have inverse:=Field.mul_inv_cancel smooth
  grind
private theorem quotient_cons (a b : Poly K) (rest : List (Poly K)) (curve : Poly K) :
    bivariateCurveQuotient (a::b::rest) curve=
      bivariateSubstitute (b::rest) curve::bivariateCurveQuotient (b::rest) curve := by
  simp [bivariateCurveQuotient,List.range_succ_eq_map,List.map_map,Function.comp_def]

/-- The local slope depends only on the curve's constant coefficient. -/
theorem hensel_slope_constant_congr (rows : List (Poly K)) (f g : Poly K)
    (same : f.coeff 0=g.coeff 0) : curveHenselSlope rows f=curveHenselSlope rows g := by
  induction rows with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      unfold curveHenselSlope at ih ⊢
      rw [quotient_cons,quotient_cons]
      simp only [bivariateSubstitute,Poly.coeff_add,product_constant]
      have sameRest:=substitute_constant_congr (b::rest) f g same
      simp only [bivariateSubstitute,Poly.coeff_add,product_constant] at sameRest
      rw [same,ih]
      grind

/-- n corrections beyond the initial constant root, retaining only the
successively constructed coefficients. -/
def curveHenselLift (rows : List (Poly K)) (a : K) : Nat→Poly K
  | 0 => Poly.C a
  | n+1 =>
    let f:=curveHenselLift rows a n
    curveHenselPerturb f (n+1) (-(bivariateSubstitute rows f).coeff (n+1)*(curveHenselSlope rows f)⁻¹)

/-- Construct a smooth formal root through any finite precision. This does
not assert convergence to a polynomial of bounded degree or an exact root. -/
theorem hensel_finite_lift (rows : List (Poly K)) (a : K)
    (root : (bivariateSubstitute rows (Poly.C a)).coeff 0=0)
    (smooth : curveHenselSlope rows (Poly.C a)≠0) (n : Nat) :
    (curveHenselLift rows a n).coeff 0=a ∧
    (curveHenselLift rows a n).DegLt (n+1) ∧
    PolynomialOrder (bivariateSubstitute rows (curveHenselLift rows a n)) (n+1) := by
  induction n with
  | zero =>
    refine ⟨rfl,?_,?_⟩
    · exact Poly.degLt_length (Poly.C a)
    · intro i hi
      have equal : i=0 := by omega
      simpa only [equal,curveHenselLift] using root
  | succ n ih =>
    let f:=curveHenselLift rows a n
    let c:=-(bivariateSubstitute rows f).coeff (n+1)*(curveHenselSlope rows f)⁻¹
    have same : f.coeff 0=(Poly.C a).coeff 0 := ih.1
    have slope : curveHenselSlope rows f≠0 := by rw [hensel_slope_constant_congr rows f (Poly.C a) same];exact smooth
    have step:=hensel_coefficient_step rows f (n+1) (by omega) ih.2.2 slope
    refine ⟨?_,?_,step⟩
    · change (f+Poly.smul c (jetMonomial (n+1))).coeff 0=a
      rw [Poly.coeff_add,Poly.coeff_smul,jet_monomial_coefficient,ite_eq_right (by omega)]
      change f.coeff 0+c*0=a
      have h:=ih.1
      grind
    · change (f+Poly.smul c (jetMonomial (n+1))).DegLt (n+1+1)
      apply Poly.degLt_add (Poly.DegLt.mono ih.2.1 (by omega))
      apply Poly.degLt_smul
      intro i hi
      rw [jet_monomial_coefficient,ite_eq_right (by omega)]

/-- Smooth roots with the same initial value are unique modulo X^n.
No exact-root assumption and no degree bound on either approximation. -/
theorem hensel_lift_unique_modulo (rows : List (Poly K)) (f g : Poly K)
    (same : f.coeff 0=g.coeff 0) (smooth : curveHenselSlope rows f≠0)
    (n : Nat) (hf : PolynomialOrder (bivariateSubstitute rows f) n)
    (hg : PolynomialOrder (bivariateSubstitute rows g) n) : PolynomialOrder (g-f) n := by
  induction n with
  | zero => intro i hi;omega
  | succ n ih =>
    have low:=ih (fun i hi=>hf i (by omega)) (fun i hi=>hg i (by omega))
    have top : (g-f).coeff n=0 := by
      by_cases positive : 0<n
      · have h:=hensel_perturbation_coefficient rows f g n positive low
        rw [Poly.coeff_sub,hf n (by omega),hg n (by omega)] at h
        have product : (g-f).coeff n*curveHenselSlope rows f=0 := by grind
        rcases Field.of_mul_eq_zero product with entry|slope
        · exact entry
        · exact False.elim (smooth slope)
      · have zero : n=0 := by omega
        rw [zero,Poly.coeff_sub,←same]
        grind
    intro i hi
    by_cases below : i<n
    · exact low i below
    · have equal : i=n := by omega
      simpa only [equal] using top
end NearCompression
