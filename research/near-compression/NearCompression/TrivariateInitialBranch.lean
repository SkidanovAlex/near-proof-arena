import NearCompression.SymbolicHensel

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Dense Q(X,Y,Z): outer rows index Y, inner rows index X, entries are Z-polynomials. -/
def denseTrivariateSpecialize (rows : List (List (Poly K))) (z : K) : List (Poly K) :=
  rows.map (fun row=>Poly.mk (row.map (fun p=>p.eval z)))

def denseTrivariateExpressions (rows : List (List (Poly K))) : List (List (HenselExpression K)) :=
  rows.map (fun row=>row.map CommonDenominatorExpression.polynomial)

/-- Coefficients of Q(0,Y,Z). -/
def trivariateInitialRows (rows : List (List (Poly K))) : List (Poly K) :=
  rows.map (fun row=>row.getD 0 Poly.zero)

def trivariateInitialResidual (rows : List (List (Poly K))) (a : Poly K) : Poly K :=
  bivariateSubstitute (trivariateInitialRows rows) a

/-- Formal Y-slope at X=0,Y=a(Z), via the divided-difference quotient. -/
def trivariateInitialSlope (rows : List (List (Poly K))) (a : Poly K) : Poly K :=
  bivariateSubstitute (bivariateCurveQuotient (trivariateInitialRows rows) a) a

private theorem product_constant (p q : Poly K) : (p*q).coeff 0=p.coeff 0*q.coeff 0 :=
  polynomial_order_product_coefficient p q 0 0 (by intro i hi;omega) (by intro i hi;omega)

private theorem specialized_constant (row : List (Poly K)) (z : K) :
    (Poly.mk (row.map (fun p=>p.eval z))).coeff 0=(row.getD 0 Poly.zero).eval z := by
  cases row <;> rfl

/-- Evaluate the actual initial residual polynomial to obtain the numeric
initial-root equation. No separate equation oracle is assumed. -/
theorem trivariate_initial_residual_eval (rows : List (List (Poly K))) (a : Poly K) (z : K) :
    (trivariateInitialResidual rows a).eval z=
      (bivariateSubstitute (denseTrivariateSpecialize rows z) (Poly.C (a.eval z))).coeff 0 := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [trivariateInitialResidual,trivariateInitialRows,denseTrivariateSpecialize,List.map_cons,
      bivariateSubstitute,Poly.eval_add,Poly.eval_mul,Poly.coeff_add,product_constant,specialized_constant] at ih ⊢
    change (row.getD 0 Poly.zero).eval z+a.eval z*(bivariateSubstitute (rest.map (fun r=>r.getD 0 Poly.zero)) a).eval z=
      (row.getD 0 Poly.zero).eval z+a.eval z*(bivariateSubstitute (denseTrivariateSpecialize rest z) (Poly.C (a.eval z))).coeff 0
    rw [ih]
    rfl

private theorem quotient_cons (p q : Poly K) (rest : List (Poly K)) (a : Poly K) :
    bivariateCurveQuotient (p::q::rest) a=
      bivariateSubstitute (q::rest) a::bivariateCurveQuotient (q::rest) a := by
  simp [bivariateCurveQuotient,List.range_succ_eq_map,List.map_map,Function.comp_def]

/-- The constructed slope specializes to the exact numeric Hensel slope. -/
theorem trivariate_initial_slope_eval (rows : List (List (Poly K))) (a : Poly K) (z : K) :
    (trivariateInitialSlope rows a).eval z=
      curveHenselSlope (denseTrivariateSpecialize rows z) (Poly.C (a.eval z)) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest =>
      simp only [trivariateInitialSlope,trivariateInitialRows,denseTrivariateSpecialize,List.map_cons,curveHenselSlope] at ih ⊢
      rw [quotient_cons,quotient_cons]
      simp only [bivariateSubstitute,Poly.eval_add,Poly.eval_mul,Poly.coeff_add,product_constant]
      have residual:=trivariate_initial_residual_eval (next::rest) a z
      simp only [trivariateInitialResidual,trivariateInitialRows,denseTrivariateSpecialize,List.map_cons,bivariateSubstitute,
        Poly.eval_add,Poly.eval_mul,Poly.coeff_add,product_constant,specialized_constant] at residual
      have ac : (Poly.C (a.eval z)).coeff 0=a.eval z := rfl
      rw [ac,ih]
      rw [specialized_constant]
      grind

/-- The slope degree is derived from the weighted budget of Q(0,Y,Z). -/
theorem trivariate_initial_slope_degree (rows : List (List (Poly K))) (a : Poly K)
    (w D : Nat) (initialDegree : a.DegLt (w+1))
    (weighted : BivariateWeightedDegree (trivariateInitialRows rows) w D) :
    (trivariateInitialSlope rows a).DegLt (D-w) := by
  exact bivariate_substitution_degree _ a w (D-w) initialDegree
    (bivariate_curve_quotient_degree _ a w D initialDegree weighted)

private theorem specialize_inputs (rows : List (List (Poly K))) (s : Poly K) (z : K) :
    (denseTrivariateExpressions rows).map (fun row=>specializeHenselPolynomial row s z)=
      denseTrivariateSpecialize rows z := by
  simp only [denseTrivariateExpressions,denseTrivariateSpecialize,specializeHenselPolynomial,List.map_map,Function.comp_def,
    specializeHenselExpression,CommonDenominatorExpression.expand,RationalExpression.eval]

/-- Generic lifting with the initial-root and slope obligations discharged
from actual dense trivariate coefficients. A polynomial initial branch is
still an explicit hypothesis, not a substitute for algebraic-factor selection. -/
theorem trivariate_initial_branch_lift (rows : List (List (Poly K))) (a : Poly K)
    (initial : (trivariateInitialResidual rows a).IsZero) (z : K)
    (good : (trivariateInitialSlope rows a).eval z≠0) (n : Nat) :
    specializeHenselPolynomial (symbolicHenselLift (denseTrivariateExpressions rows) (.polynomial a) n)
      (trivariateInitialSlope rows a) z=
      curveHenselLift (denseTrivariateSpecialize rows z) (a.eval z) n := by
  have residual : (bivariateSubstitute (denseTrivariateSpecialize rows z) (Poly.C (a.eval z))).coeff 0=0 := by
    rw [←trivariate_initial_residual_eval]
    exact Poly.eval_of_isZero initial z
  have actualSlope:=trivariate_initial_slope_eval rows a z
  have result:=symbolic_hensel_specializes (denseTrivariateExpressions rows) (.polynomial a)
    (trivariateInitialSlope rows a) z
    (by simpa only [specialize_inputs,specializeHenselExpression,CommonDenominatorExpression.expand,RationalExpression.eval] using residual)
    (by simpa only [specialize_inputs,specializeHenselExpression,CommonDenominatorExpression.expand,RationalExpression.eval] using actualSlope.symm)
    good n
  simpa only [specialize_inputs,specializeHenselExpression,CommonDenominatorExpression.expand,RationalExpression.eval] using result
/-- Explicit slope-zero challenge budget derived from the input weighted
degree. Nonzero formal slope is required; singular branches are not covered. -/
theorem trivariate_initial_slope_root_count (rows : List (List (Poly K))) (a : Poly K)
    (w D : Nat) (initialDegree : a.DegLt (w+1))
    (weighted : BivariateWeightedDegree (trivariateInitialRows rows) w D)
    (nonzero : ¬(trivariateInitialSlope rows a).IsZero)
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun z=>(trivariateInitialSlope rows a).eval z=0)≤D-w-1 := by
  have bound:=PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval K
    (trivariateInitialSlope rows a) (D-w) sample nonzero
    (trivariate_initial_slope_degree rows a w D initialDegree weighted) distinct
  omega
end NearCompression
