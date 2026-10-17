import NearCompression.CommonDenominator

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

abbrev HenselExpression (K : Type) := CommonDenominatorExpression K

def henselExpressionZero : HenselExpression K := .polynomial Poly.zero

def specializeHenselExpression (e : HenselExpression K) (s : Poly K) (z : K) : K :=
  (e.expand s).eval z

def specializeHenselPolynomial (f : List (HenselExpression K)) (s : Poly K) (z : K) : Poly K :=
  Poly.mk (f.map (fun e=>specializeHenselExpression e s z))

def henselExpressionAdd : List (HenselExpression K)→List (HenselExpression K)→List (HenselExpression K)
  | [],g => g
  | f,[] => f
  | a::f,b::g => .add a b::henselExpressionAdd f g

def henselExpressionMul : List (HenselExpression K)→List (HenselExpression K)→List (HenselExpression K)
  | [],_ => []
  | a::f,g => henselExpressionAdd (g.map (fun b=>.mul a b))
      (henselExpressionZero::henselExpressionMul f g)

def henselExpressionSubstitute : List (List (HenselExpression K))→List (HenselExpression K)→List (HenselExpression K)
  | [],_ => []
  | row::rest,f => henselExpressionAdd row (henselExpressionMul f (henselExpressionSubstitute rest f))

def henselExpressionPerturb (f : List (HenselExpression K)) (n : Nat) (c : HenselExpression K) :=
  henselExpressionAdd f ((List.range (n+1)).map (fun i=>if i=n then c else henselExpressionZero))

private theorem eval_zero (s : Poly K) (z : K) : specializeHenselExpression henselExpressionZero s z=0 := rfl
private theorem eval_add (a b : HenselExpression K) (s : Poly K) (z : K) :
    specializeHenselExpression (.add a b) s z=specializeHenselExpression a s z+specializeHenselExpression b s z := rfl
private theorem eval_mul (a b : HenselExpression K) (s : Poly K) (z : K) :
    specializeHenselExpression (.mul a b) s z=specializeHenselExpression a s z*specializeHenselExpression b s z := rfl

private theorem map_add (f g : List (HenselExpression K)) (s : Poly K) (z : K) :
    (henselExpressionAdd f g).map (fun e=>specializeHenselExpression e s z)=
      Poly.addL (f.map (fun e=>specializeHenselExpression e s z))
        (g.map (fun e=>specializeHenselExpression e s z)) := by
  induction f generalizing g with
  | nil => rfl
  | cons a f ih =>
    cases g with
    | nil => rfl
    | cons b g => simp only [henselExpressionAdd,List.map_cons,eval_add,Poly.addL,ih]

/-- Symbolic padded polynomial addition specializes exactly. -/
theorem specialize_hensel_add (f g : List (HenselExpression K)) (s : Poly K) (z : K) :
    specializeHenselPolynomial (henselExpressionAdd f g) s z=
      specializeHenselPolynomial f s z+specializeHenselPolynomial g s z :=
  congrArg Poly.mk (map_add f g s z)

private theorem map_mul (f g : List (HenselExpression K)) (s : Poly K) (z : K) :
    (henselExpressionMul f g).map (fun e=>specializeHenselExpression e s z)=
      Poly.mulL (f.map (fun e=>specializeHenselExpression e s z))
        (g.map (fun e=>specializeHenselExpression e s z)) := by
  induction f with
  | nil => rfl
  | cons a f ih =>
    simp only [henselExpressionMul,map_add,List.map_cons,eval_zero,ih,Poly.mulL,Poly.scaleL,List.map_map,Function.comp_def,eval_mul]

/-- Symbolic schoolbook multiplication specializes exactly, including padding. -/
theorem specialize_hensel_mul (f g : List (HenselExpression K)) (s : Poly K) (z : K) :
    specializeHenselPolynomial (henselExpressionMul f g) s z=
      specializeHenselPolynomial f s z*specializeHenselPolynomial g s z :=
  congrArg Poly.mk (map_mul f g s z)

/-- Symbolic bivariate substitution specializes to the existing formal polynomial. -/
theorem specialize_hensel_substitution (rows : List (List (HenselExpression K)))
    (f : List (HenselExpression K)) (s : Poly K) (z : K) :
    specializeHenselPolynomial (henselExpressionSubstitute rows f) s z=
      bivariateSubstitute (rows.map (fun row=>specializeHenselPolynomial row s z))
        (specializeHenselPolynomial f s z) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [henselExpressionSubstitute,specialize_hensel_add,specialize_hensel_mul,ih,List.map_cons,bivariateSubstitute]

private theorem specialize_coefficient (f : List (HenselExpression K)) (s : Poly K) (z : K) (i : Nat) :
    specializeHenselExpression (f.getD i henselExpressionZero) s z=
      (specializeHenselPolynomial f s z).coeff i := by
  induction f generalizing i with
  | nil => simp only [List.getD_nil,eval_zero];rfl
  | cons a f ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

/-- Updating a symbolic coefficient specializes to the numeric Hensel update. -/
theorem specialize_hensel_perturb (f : List (HenselExpression K)) (s : Poly K) (z : K)
    (n : Nat) (c : HenselExpression K) :
    specializeHenselPolynomial (henselExpressionPerturb f n c) s z=
      curveHenselPerturb (specializeHenselPolynomial f s z) n (specializeHenselExpression c s z) := by
  unfold henselExpressionPerturb curveHenselPerturb
  rw [specialize_hensel_add]
  congr 1
  unfold specializeHenselPolynomial Poly.smul Poly.scaleL jetMonomial
  congr 1
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i hi
  by_cases equal : i=n
  · simp only [equal,ite_true];grind
  · simp only [equal,ite_false,eval_zero];grind

/-- Symbolic lift; every correction reuses the designated reciprocal1/S. -/
def symbolicHenselLift (rows : List (List (HenselExpression K))) (a : HenselExpression K) :
    Nat→List (HenselExpression K)
  | 0 => [a]
  | n+1 =>
    let f:=symbolicHenselLift rows a n
    let residual:=(henselExpressionSubstitute rows f).getD (n+1) henselExpressionZero
    henselExpressionPerturb f (n+1) (.mul (.neg residual) .reciprocal)

/-- Generic symbolic/numeric Hensel correspondence. S must equal the actual
initial slope at the challenge; that premise is not replaced by mere S≠0. -/
theorem symbolic_hensel_specializes (rows : List (List (HenselExpression K)))
    (a : HenselExpression K) (s : Poly K) (z : K)
    (initial : (bivariateSubstitute (rows.map (fun row=>specializeHenselPolynomial row s z))
      (Poly.C (specializeHenselExpression a s z))).coeff 0=0)
    (slope : curveHenselSlope (rows.map (fun row=>specializeHenselPolynomial row s z))
      (Poly.C (specializeHenselExpression a s z))=s.eval z)
    (good : s.eval z≠0) (n : Nat) :
    specializeHenselPolynomial (symbolicHenselLift rows a n) s z=
      curveHenselLift (rows.map (fun row=>specializeHenselPolynomial row s z))
        (specializeHenselExpression a s z) n := by
  let rs:=rows.map (fun row=>specializeHenselPolynomial row s z)
  let av:=specializeHenselExpression a s z
  have smooth : curveHenselSlope rs (Poly.C av)≠0 := by rw [slope];exact good
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [symbolicHenselLift,specialize_hensel_perturb,ih]
    have constant:=(hensel_finite_lift rs av initial smooth n).1
    have currentSlope : curveHenselSlope rs (curveHenselLift rs av n)=s.eval z :=
      (hensel_slope_constant_congr rs _ (Poly.C av) constant).trans slope
    change curveHenselPerturb _ (n+1)
      (-specializeHenselExpression ((henselExpressionSubstitute rows (symbolicHenselLift rows a n)).getD (n+1) henselExpressionZero) s z*(s.eval z)⁻¹)=_
    rw [specialize_coefficient,specialize_hensel_substitution,ih]
    change curveHenselPerturb (curveHenselLift rs av n) (n+1)
      (-(bivariateSubstitute rs (curveHenselLift rs av n)).coeff (n+1)*(s.eval z)⁻¹)=_
    rw [←currentSlope]
    rfl
/-- Many bounded-degree specialized roots force a higher symbolic lift
coefficient's normalized numerator to vanish formally. This does not supply
useful factors, a common initial branch, or the numerator-degree budget. -/
theorem symbolic_hensel_high_coefficient_zero
    (rows : List (List (HenselExpression K))) (a : HenselExpression K) (s : Poly K)
    (n k i D : Nat) (precision : k≤n) (high : k<i)
    (degree : (((symbolicHenselLift rows a n).getD i henselExpressionZero).normalize s).1.DegLt D)
    (sample : List K) (distinct : sample.Nodup) (enough : D≤sample.length)
    (good : ∀ z∈sample,s.eval z≠0)
    (initial : ∀ z∈sample,
      (bivariateSubstitute (rows.map (fun row=>specializeHenselPolynomial row s z))
        (Poly.C (specializeHenselExpression a s z))).coeff 0=0)
    (slope : ∀ z∈sample,
      curveHenselSlope (rows.map (fun row=>specializeHenselPolynomial row s z))
        (Poly.C (specializeHenselExpression a s z))=s.eval z)
    (candidates : ∀ z∈sample,∃ f : Poly K,
      f.coeff 0=specializeHenselExpression a s z ∧ f.DegLt (k+1) ∧
      (bivariateSubstitute (rows.map (fun row=>specializeHenselPolynomial row s z)) f).IsZero) :
    (((symbolicHenselLift rows a n).getD i henselExpressionZero).normalize s).1.IsZero := by
  apply common_denominator_zero_of_specializations _ s D degree sample distinct enough good
  intro z member
  change specializeHenselExpression ((symbolicHenselLift rows a n).getD i henselExpressionZero) s z=0
  rw [specialize_coefficient,symbolic_hensel_specializes rows a s z (initial z member) (slope z member) (good z member)]
  obtain ⟨f,constant,bounded,root⟩:=candidates z member
  let rs:=rows.map (fun row=>specializeHenselPolynomial row s z)
  have same : f.coeff 0=(Poly.C (specializeHenselExpression a s z)).coeff 0 := constant
  have smooth : curveHenselSlope rs f≠0 := by
    rw [hensel_slope_constant_congr rs f _ same,slope z member]
    exact good z member
  have equal:=hensel_reconstruct_bounded_root rs f n (Poly.DegLt.mono bounded (by omega)) root smooth
  rw [constant] at equal
  rw [equal i]
  exact bounded i (by omega)
end NearCompression
