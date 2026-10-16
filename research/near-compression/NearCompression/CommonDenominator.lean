import NearCompression.RationalSpecialization

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def denominatorPower (s : Poly K) : Nat→Poly K
  | 0 => Poly.C 1
  | n+1 => s*denominatorPower s n

theorem denominator_power_eval (s : Poly K) (n : Nat) (z : K) :
    (denominatorPower s n).eval z=(s.eval z)^n := by
  induction n with
  | zero => simp only [denominatorPower,Poly.eval_C,Semiring.pow_zero]
  | succ n ih => simp only [denominatorPower,Poly.eval_mul,ih,Semiring.pow_succ];grind

theorem denominator_power_degree (s : Poly K) (d n : Nat) (degree : s.DegLt (d+1)) :
    (denominatorPower s n).DegLt (d*n+1) := by
  induction n with
  | zero => exact Poly.degLt_length (Poly.C 1)
  | succ n ih =>
    have h:=Poly.degLt_mul degree ih
    have equal : d+d*n+1=d*(n+1)+1 := by grind
    simpa only [equal,denominatorPower] using h

/-- Arithmetic using polynomial leaves and one designated reciprocal 1/S.
Arbitrary inversions are deliberately not constructors of this interface. -/
inductive CommonDenominatorExpression (K : Type) where
  | polynomial : Poly K→CommonDenominatorExpression K
  | reciprocal : CommonDenominatorExpression K
  | add : CommonDenominatorExpression K→CommonDenominatorExpression K→CommonDenominatorExpression K
  | mul : CommonDenominatorExpression K→CommonDenominatorExpression K→CommonDenominatorExpression K
  | neg : CommonDenominatorExpression K→CommonDenominatorExpression K

open CommonDenominatorExpression

def CommonDenominatorExpression.expand (s : Poly K) : CommonDenominatorExpression K→RationalExpression K
  | polynomial p => .polynomial p
  | reciprocal => .inv (.polynomial s)
  | add a b => .add (a.expand s) (b.expand s)
  | mul a b => .mul (a.expand s) (b.expand s)
  | neg a => .neg (a.expand s)

/-- Normalize as numerator/S^exponent, aligning sums at the larger exponent. -/
def CommonDenominatorExpression.normalize (s : Poly K) : CommonDenominatorExpression K→Poly K×Nat
  | polynomial p => (p,0)
  | reciprocal => (Poly.C 1,1)
  | add a b =>
    let x:=a.normalize s
    let y:=b.normalize s
    let m:=max x.2 y.2
    (x.1*denominatorPower s (m-x.2)+y.1*denominatorPower s (m-y.2),m)
  | mul a b =>
    let x:=a.normalize s
    let y:=b.normalize s
    (x.1*y.1,x.2+y.2)
  | neg a => (-(a.normalize s).1,(a.normalize s).2)

/-- All expanded arithmetic is valid away from the roots of S. -/
theorem common_denominator_safe (e : CommonDenominatorExpression K) (s : Poly K) (z : K)
    (good : s.eval z≠0) : (e.expand s).SafeAt z := by
  induction e with
  | polynomial p => trivial
  | reciprocal => exact ⟨True.intro,good⟩
  | add a b ia ib => exact ⟨ia,ib⟩
  | mul a b ia ib => exact ⟨ia,ib⟩
  | neg a ia => exact ia

/-- Exact common-power evaluation identity on the original expression's
safe domain. No polynomial-function equality is used to infer coefficients. -/
theorem common_denominator_normalization (e : CommonDenominatorExpression K) (s : Poly K) (z : K)
    (good : s.eval z≠0) :
    (s.eval z)^((e.normalize s).2)*(e.expand s).eval z=(e.normalize s).1.eval z := by
  induction e with
  | polynomial p => simp only [CommonDenominatorExpression.normalize,CommonDenominatorExpression.expand,RationalExpression.eval,Semiring.pow_zero];grind
  | reciprocal =>
    simp only [CommonDenominatorExpression.normalize,CommonDenominatorExpression.expand,RationalExpression.eval,Poly.eval_C,Semiring.pow_one]
    exact Field.mul_inv_cancel good
  | neg a ia =>
    simp only [CommonDenominatorExpression.normalize,CommonDenominatorExpression.expand,RationalExpression.eval,Poly.eval_neg]
    grind
  | mul a b ia ib =>
    simp only [CommonDenominatorExpression.normalize,CommonDenominatorExpression.expand,RationalExpression.eval,Poly.eval_mul,Semiring.pow_add]
    grind
  | add a b ia ib =>
    let m:=max (a.normalize s).2 (b.normalize s).2
    have ea : (a.normalize s).2+(m-(a.normalize s).2)=m := by dsimp [m];omega
    have eb : (b.normalize s).2+(m-(b.normalize s).2)=m := by dsimp [m];omega
    have pa : (s.eval z)^m=(s.eval z)^((a.normalize s).2)*(s.eval z)^(m-(a.normalize s).2) := by rw [←Semiring.pow_add,ea]
    have pb : (s.eval z)^m=(s.eval z)^((b.normalize s).2)*(s.eval z)^(m-(b.normalize s).2) := by rw [←Semiring.pow_add,eb]
    simp only [CommonDenominatorExpression.normalize,CommonDenominatorExpression.expand,RationalExpression.eval,Poly.eval_add,Poly.eval_mul,denominator_power_eval]
    change (s.eval z)^m*((a.expand s).eval z+(b.expand s).eval z)=_
    grind

/-- A whole family shares the same excluded challenge set. In particular,
expression size and denominator exponents do not multiply this pole budget. -/
theorem common_denominator_family_pole_count (expressions : List (CommonDenominatorExpression K))
    (s : Poly K) (d : Nat) (nonzero : ¬s.IsZero) (degree : s.DegLt (d+1))
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun z=>∃ e∈expressions,¬(e.expand s).SafeAt z)≤d := by
  have roots:=PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval K s (d+1) sample nonzero degree distinct
  have subset : count sample (fun z=>∃ e∈expressions,¬(e.expand s).SafeAt z)≤count sample (fun z=>s.eval z=0) := by
    apply count_mono
    intro z bad
    obtain ⟨e,member,excluded⟩:=bad
    apply Classical.byContradiction
    intro good
    exact excluded (common_denominator_safe e s z good)
  omega
/-- Degree bound for the normalized numerator, paired with its denominator
exponent. S has degree at most d; addition aligns exponents using max. -/
def commonDenominatorBudget (d : Nat) : CommonDenominatorExpression K→Nat×Nat
  | polynomial p => (p.coeffs.length-1,0)
  | reciprocal => (0,1)
  | add a b =>
    let x:=commonDenominatorBudget d a
    let y:=commonDenominatorBudget d b
    let m:=max x.2 y.2
    (max (x.1+d*(m-x.2)) (y.1+d*(m-y.2)),m)
  | mul a b =>
    let x:=commonDenominatorBudget d a
    let y:=commonDenominatorBudget d b
    (x.1+y.1,x.2+y.2)
  | neg a => commonDenominatorBudget d a

/-- Normalization realizes the claimed exponent and numerator-degree budget. -/
theorem common_denominator_degree (e : CommonDenominatorExpression K) (s : Poly K)
    (d : Nat) (degree : s.DegLt (d+1)) :
    (e.normalize s).2=(commonDenominatorBudget d e).2 ∧
    (e.normalize s).1.DegLt ((commonDenominatorBudget d e).1+1) := by
  induction e with
  | polynomial p => exact ⟨rfl,Poly.DegLt.mono (Poly.degLt_length p) (by simp only [commonDenominatorBudget];omega)⟩
  | reciprocal => exact ⟨rfl,Poly.degLt_length (Poly.C 1)⟩
  | neg a ia => exact ⟨ia.1,Poly.degLt_neg ia.2⟩
  | mul a b ia ib =>
    exact ⟨by simp only [CommonDenominatorExpression.normalize,commonDenominatorBudget,ia.1,ib.1],Poly.degLt_mul ia.2 ib.2⟩
  | add a b ia ib =>
    simp only [CommonDenominatorExpression.normalize,commonDenominatorBudget]
    rw [ia.1,ib.1]
    refine ⟨rfl,Poly.degLt_add ?_ ?_⟩
    · exact Poly.DegLt.mono (Poly.degLt_mul ia.2 (denominator_power_degree s d _ degree)) (by omega)
    · exact Poly.DegLt.mono (Poly.degLt_mul ib.2 (denominator_power_degree s d _ degree)) (by omega)

/-- Enough safe zero specializations force the actual normalized numerator
polynomial to vanish formally. Unsafe challenges cannot be used as roots. -/
theorem common_denominator_zero_of_specializations (e : CommonDenominatorExpression K)
    (s : Poly K) (D : Nat) (degree : (e.normalize s).1.DegLt D)
    (sample : List K) (distinct : sample.Nodup) (enough : D≤sample.length)
    (good : ∀ z∈sample,s.eval z≠0)
    (zeros : ∀ z∈sample,(e.expand s).eval z=0) : (e.normalize s).1.IsZero := by
  apply PolyRoots.eqZeroOfRoots_of polyEval polyDeg quotFacts isZeroEval K _ D sample degree distinct enough
  intro z member
  have identity:=common_denominator_normalization e s z (good z member)
  rw [zeros z member] at identity
  grind
end NearCompression
