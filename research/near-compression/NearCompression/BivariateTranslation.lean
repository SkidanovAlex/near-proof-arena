import NearCompression.BivariateMultiplicity

/-! Translation/substitution with an explicit sufficient evaluation domain.
Coefficient equality follows from degree bounds and distinct-point uniqueness,
never from arbitrary equality of finite-field functions. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def polynomialTranslate (p : Poly K) (a : K) : Poly K :=
  Poly.mk (syntheticTaylor p a p.coeffs.length)

theorem polynomial_translate_eval (p : Poly K) (a x : K) :
    (polynomialTranslate p a).eval x=p.eval (a+x) :=
  synthetic_taylor_evaluation p.coeffs.length p a x (Poly.degLt_length p)

private theorem jet_of_degree (i : Nat) (p : Poly K) (degree : p.DegLt i) (a : K) :
    syntheticJet p a i=0 := by
  induction i generalizing p with
  | zero => exact Poly.eval_of_isZero (fun j=>degree j (Nat.zero_le j)) a
  | succ i ih => exact ih (p.quot a) (Poly.degLt_quot p a degree)

private theorem taylor_length (p : Poly K) (a : K) (n : Nat) :
    (syntheticTaylor p a n).length=n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp [syntheticTaylor,ih]

/-- All translated coefficients equal jets, including beyond the stored list. -/
theorem polynomial_translate_coeff (p : Poly K) (a : K) (i : Nat) :
    (polynomialTranslate p a).coeff i=syntheticJet p a i := by
  by_cases inside : i<p.coeffs.length
  · exact synthetic_taylor_coefficient p.coeffs.length p a i inside
  · have degree:=Poly.DegLt.mono (Poly.degLt_length p) (show p.coeffs.length≤i by omega)
    rw [jet_of_degree i p degree a]
    apply Poly.degLt_length (polynomialTranslate p a) i
    simpa only [polynomialTranslate,taylor_length] using (show p.coeffs.length≤i by omega)

def bivariateEval : List (Poly K)→K→K→K
  | [],_,_ => 0
  | row::rest,x,y => row.eval x+y*bivariateEval rest x y

private theorem substitution_eval (rows : List (Poly K)) (curve : Poly K) (x : K) :
    (bivariateSubstitute rows curve).eval x=bivariateEval rows x (curve.eval x) := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [bivariateSubstitute,bivariateEval,Poly.eval_add,Poly.eval_mul,ih]

def bivariateAddRows : List (Poly K)→List (Poly K)→List (Poly K)
  | [],ys => ys
  | xs,[] => xs
  | x::xs,y::ys => (x+y)::bivariateAddRows xs ys

private theorem rows_add_eval (xs ys : List (Poly K)) (x y : K) :
    bivariateEval (bivariateAddRows xs ys) x y=bivariateEval xs x y+bivariateEval ys x y := by
  induction xs generalizing ys with
  | nil => simp only [bivariateAddRows,bivariateEval];grind
  | cons r rs ih =>
    cases ys with
    | nil => simp only [bivariateAddRows,bivariateEval];grind
    | cons s ss => simp only [bivariateAddRows,bivariateEval,Poly.eval_add,ih];grind

private theorem rows_scale_eval (rows : List (Poly K)) (b x y : K) :
    bivariateEval (rows.map (Poly.smul b)) x y=b*bivariateEval rows x y := by
  induction rows with
  | nil => simp only [List.map_nil,bivariateEval];grind
  | cons row rest ih => simp only [List.map_cons,bivariateEval,Poly.eval_smul,ih];grind

def bivariateTranslateY : List (Poly K)→K→List (Poly K)
  | [],_ => []
  | row::rest,b =>
    let tail:=bivariateTranslateY rest b
    bivariateAddRows [row] (bivariateAddRows (tail.map (Poly.smul b)) (Poly.zero::tail))

private theorem translate_y_eval (rows : List (Poly K)) (b x y : K) :
    bivariateEval (bivariateTranslateY rows b) x y=bivariateEval rows x (b+y) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [bivariateTranslateY,rows_add_eval,rows_scale_eval,bivariateEval,Poly.zero,Poly.eval,Poly.evalL]
    change row.eval x+y*0+(b*bivariateEval (bivariateTranslateY rest b) x y+
      (0+y*bivariateEval (bivariateTranslateY rest b) x y))=
      row.eval x+(b+y)*bivariateEval rest x (b+y)
    rw [ih];grind

def bivariateTranslate (rows : List (Poly K)) (a b : K) : List (Poly K) :=
  bivariateTranslateY (rows.map (fun row=>polynomialTranslate row a)) b

theorem bivariate_translate_eval (rows : List (Poly K)) (a b x y : K) :
    bivariateEval (bivariateTranslate rows a b) x y=bivariateEval rows (a+x) (b+y) := by
  unfold bivariateTranslate
  rw [translate_y_eval]
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [List.map_cons,bivariateEval,polynomial_translate_eval,ih]

def centeredCurve (curve : Poly K) (a : K) : Poly K :=
  polynomialTranslate curve a-Poly.C (curve.eval a)

/-- Formal jet conclusion at any center. The sample must separate two
specified polynomials: both degrees are bounded by D, with D distinct points.
These are explicit algebraic hypotheses, not cryptographic sampling. -/
theorem bivariate_substitution_at_center (rows : List (Poly K)) (curve : Poly K)
    (a : K) (m D : Nat) (sample : List K) (distinct : sample.Nodup) (enough : D≤sample.length)
    (leftDegree : (polynomialTranslate (bivariateSubstitute rows curve) a).DegLt D)
    (rightDegree : (bivariateSubstitute (bivariateTranslate rows a (curve.eval a))
      (centeredCurve curve a)).DegLt D)
    (mixed : BivariateOrder (bivariateTranslate rows a (curve.eval a)) m) :
    ∀ i<m,syntheticJet (bivariateSubstitute rows curve) a i=0 := by
  let left:=polynomialTranslate (bivariateSubstitute rows curve) a
  let right:=bivariateSubstitute (bivariateTranslate rows a (curve.eval a)) (centeredCurve curve a)
  have evals : ∀ x,left.eval x=right.eval x := by
    intro x
    dsimp only [left,right]
    rw [polynomial_translate_eval,substitution_eval,substitution_eval,bivariate_translate_eval]
    have cv : (centeredCurve curve a).eval x=curve.eval (a+x)-curve.eval a := by
      unfold centeredCurve
      rw [Poly.eval_sub,polynomial_translate_eval]
      have constant : (Poly.C (curve.eval a)).eval x=curve.eval a := by
        simp only [Poly.C,Poly.eval,Poly.evalL];grind
      rw [constant]
    rw [cv]
    have cancel : curve.eval a+(curve.eval (a+x)-curve.eval a)=curve.eval (a+x) := by grind
    rw [cancel]
  have zero : (left-right).IsZero := by
    apply PolyRoots.eqZeroOfRoots_of polyEval polyDeg quotFacts isZeroEval K (left-right) D sample
    · exact Poly.degLt_sub leftDegree rightDegree
    · exact distinct
    · exact enough
    · intro x hx;rw [Poly.eval_sub,evals x];grind
  have through : (centeredCurve curve a).coeff 0=0 := by
    rw [centeredCurve,Poly.coeff_sub,polynomial_translate_coeff]
    change curve.eval a-(Poly.C (curve.eval a)).coeff 0=0
    simp only [Poly.C,Poly.coeff,List.getD,List.getElem?_cons_zero,Option.getD_some]
    grind
  have order:=bivariate_substitution_order m (bivariateTranslate rows a (curve.eval a))
    (centeredCurve curve a) through mixed
  intro i hi
  have equal:=zero i
  rw [Poly.coeff_sub] at equal
  have low:=order i hi
  change right.coeff i=0 at low
  change left.coeff i-right.coeff i=0 at equal
  dsimp only [left] at equal
  rw [polynomial_translate_coeff,low] at equal
  grind
/-- GS root-forcing step with explicit coefficient-size separation. Mixed
multiplicity at the graph points forces the substitution to be formally zero
once total multiplicity reaches its degree bound. Interpolant existence and
its weighted-degree bound are separate obligations. -/
theorem bivariate_multiplicity_forces_zero (rows : List (Poly K)) (curve : Poly K)
    (centers : List K) (centerDistinct : centers.Nodup) (multiplicity : K→Nat)
    (D : Nat) (degree : (bivariateSubstitute rows curve).DegLt D)
    (total : D≤(centers.map multiplicity).sum)
    (sample : List K) (sampleDistinct : sample.Nodup)
    (separation : ∀ a∈centers,
      max (polynomialTranslate (bivariateSubstitute rows curve) a).coeffs.length
        (bivariateSubstitute (bivariateTranslate rows a (curve.eval a))
          (centeredCurve curve a)).coeffs.length≤sample.length)
    (mixed : ∀ a∈centers,BivariateOrder (bivariateTranslate rows a (curve.eval a)) (multiplicity a)) :
    (bivariateSubstitute rows curve).IsZero := by
  have jets : ∀ a∈centers,∀ i<multiplicity a,syntheticJet (bivariateSubstitute rows curve) a i=0 := by
    intro a ha
    let bound:=max (polynomialTranslate (bivariateSubstitute rows curve) a).coeffs.length
      (bivariateSubstitute (bivariateTranslate rows a (curve.eval a)) (centeredCurve curve a)).coeffs.length
    apply bivariate_substitution_at_center rows curve a (multiplicity a) bound sample sampleDistinct (separation a ha)
    · exact Poly.DegLt.mono (Poly.degLt_length _) (Nat.le_max_left _ _)
    · exact Poly.DegLt.mono (Poly.degLt_length _) (Nat.le_max_right _ _)
    · exact mixed a ha
  apply Classical.byContradiction
  intro nonzero
  have bound:=synthetic_multipoint_bound centers centerDistinct multiplicity D
    (bivariateSubstitute rows curve) degree nonzero jets
  omega
end NearCompression
