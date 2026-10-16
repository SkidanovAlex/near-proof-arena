import NearCompression.TrivariateRootForcing

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Synthetic quotient by the monic polynomial Y-curve(X). Rows are in Y. -/
def bivariateCurveQuotient (rows : List (Poly K)) (curve : Poly K) : List (Poly K) :=
  (List.range (rows.length-1)).map (fun j=>bivariateSubstitute (rows.drop (j+1)) curve)

theorem bivariate_curve_quotient_length (rows : List (Poly K)) (curve : Poly K) :
    (bivariateCurveQuotient rows curve).length=rows.length-1 := by
  simp [bivariateCurveQuotient]

private theorem quotient_row (rows : List (Poly K)) (curve : Poly K) (j : Nat) :
    (bivariateCurveQuotient rows curve).getD j Poly.zero=
      bivariateSubstitute (rows.drop (j+1)) curve := by
  by_cases inside : j<rows.length-1
  · simp [bivariateCurveQuotient,List.getD,inside]
  · have outside : rows.length≤j+1 := by omega
    have past : rows.length-1≤j := by omega
    simp [bivariateCurveQuotient,List.getD,inside,List.drop_eq_nil_of_le outside,bivariateSubstitute]

private theorem product_zero (curve : Poly K) (i : Nat) : (curve*Poly.zero).coeff i=0 := by
  have bound:=polynomial_order_mul 0 (i+1) curve Poly.zero
    (by intro j hj;omega) (by intro j hj;rfl)
  exact bound i (by omega)

private theorem substitution_drop (rows : List (Poly K)) (curve : Poly K) (j i : Nat) :
    (bivariateSubstitute (rows.drop j) curve).coeff i=
      (rows.getD j Poly.zero).coeff i+
        (curve*bivariateSubstitute (rows.drop (j+1)) curve).coeff i := by
  induction rows generalizing j with
  | nil =>
    simp only [List.drop_nil,List.getD_nil,bivariateSubstitute]
    change (Poly.zero : Poly K).coeff i=(Poly.zero : Poly K).coeff i+(curve*Poly.zero).coeff i
    rw [product_zero];grind
  | cons row rest ih =>
    cases j with
    | zero => exact Poly.coeff_add row _ i
    | succ j => simpa only [List.drop_succ_cons,List.getD_cons_succ] using ih j

/-- Exact coefficient identity Q=(Y-curve)*quotient+Q(X,curve(X)).
No evaluation-domain or field-size assumption is needed. -/
theorem bivariate_curve_division (rows : List (Poly K)) (curve : Poly K) (i j : Nat) :
    (rows.getD j Poly.zero).coeff i=
      (if j=0 then (bivariateSubstitute rows curve).coeff i
       else ((bivariateCurveQuotient rows curve).getD (j-1) Poly.zero).coeff i)-
      (curve*((bivariateCurveQuotient rows curve).getD j Poly.zero)).coeff i := by
  simp only [quotient_row]
  cases j with
  | zero =>
    simp only [ite_true]
    have h:=substitution_drop rows curve 0 i
    simp only [List.drop_zero] at h
    grind
  | succ j =>
    simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel]
    have h:=substitution_drop rows curve (j+1) i
    grind

/-- Coefficient formula for multiplying a Y-polynomial by Y-curve(X). -/
def bivariateCurveFactorCoefficient (quotient : List (Poly K)) (curve : Poly K) (i j : Nat) : K :=
  (if j=0 then 0 else (quotient.getD (j-1) Poly.zero).coeff i)-
    (curve*(quotient.getD j Poly.zero)).coeff i

/-- A formal polynomial root is equivalent to a formal monic linear factor,
with an explicit quotient having one fewer stored Y row. -/
theorem bivariate_curve_factor_iff (rows : List (Poly K)) (curve : Poly K) :
    (bivariateSubstitute rows curve).IsZero ↔
      ∀ i j,(rows.getD j Poly.zero).coeff i=
        bivariateCurveFactorCoefficient (bivariateCurveQuotient rows curve) curve i j := by
  constructor
  · intro root i j
    rw [bivariate_curve_division rows curve i j]
    simp only [bivariateCurveFactorCoefficient,root i]
  · intro factor i
    have division:=bivariate_curve_division rows curve i 0
    have h:=factor i 0
    simp only [bivariateCurveFactorCoefficient,ite_true] at h division
    grind
/-- Factoring a root of a nonzero polynomial cannot produce a zero quotient. -/
theorem bivariate_curve_quotient_nonzero (rows : List (Poly K)) (curve : Poly K)
    (nonzero : ∃ i j,(rows.getD j Poly.zero).coeff i≠0)
    (root : (bivariateSubstitute rows curve).IsZero) :
    ∃ i j,((bivariateCurveQuotient rows curve).getD j Poly.zero).coeff i≠0 := by
  apply Classical.byContradiction
  intro none
  have zero (i j : Nat) : ((bivariateCurveQuotient rows curve).getD j Poly.zero).coeff i=0 := by
    apply Classical.byContradiction
    intro h
    exact none ⟨i,j,h⟩
  obtain ⟨i,j,entry⟩:=nonzero
  have factor:=(bivariate_curve_factor_iff rows curve).mp root i j
  have product:=polynomial_order_mul 0 (i+1) curve
    ((bivariateCurveQuotient rows curve).getD j Poly.zero)
    (by intro t ht;omega) (fun t _=>zero t j)
  have vanishes:=product i (by omega)
  simp only [bivariateCurveFactorCoefficient,zero,vanishes] at factor
  split at factor <;> apply entry <;> grind

private theorem weighted_drop (rows : List (Poly K)) (k D n : Nat)
    (weighted : BivariateWeightedDegree rows k D) :
    BivariateWeightedDegree (rows.drop n) k (D-k*n) := by
  intro i j bound
  have expanded : k*(n+j)=k*n+k*j := by grind
  have h:=weighted i (n+j) (by rw [expanded];omega)
  simpa only [List.getD,List.getElem?_drop] using h

/-- Division by Y-curve consumes weight k when degree(curve)≤k. -/
theorem bivariate_curve_quotient_degree (rows : List (Poly K)) (curve : Poly K)
    (k D : Nat) (degree : curve.DegLt (k+1))
    (weighted : BivariateWeightedDegree rows k D) :
    BivariateWeightedDegree (bivariateCurveQuotient rows curve) k (D-k) := by
  apply (bivariate_weighted_degree_rows _ k (D-k)).mpr
  intro j
  rw [quotient_row]
  have bound:=bivariate_substitution_degree (rows.drop (j+1)) curve k
    (D-k*(j+1)) degree (weighted_drop rows k D (j+1) weighted)
  have expanded : k*(j+1)=k*j+k := by grind
  have equal : D-k*(j+1)=(D-k)-k*j := by rw [expanded];omega
  simpa only [equal] using bound
end NearCompression
