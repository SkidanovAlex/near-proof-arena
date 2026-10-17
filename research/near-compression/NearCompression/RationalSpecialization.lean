import NearCompression.HenselBoundedReconstruction

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- Arithmetic expressions in Z with explicit inversions. These are not a
quotient-field implementation; specialization preserves every syntactic pole. -/
inductive RationalExpression (K : Type) where
  | polynomial : Poly K→RationalExpression K
  | add : RationalExpression K→RationalExpression K→RationalExpression K
  | mul : RationalExpression K→RationalExpression K→RationalExpression K
  | neg : RationalExpression K→RationalExpression K
  | inv : RationalExpression K→RationalExpression K

open RationalExpression
variable {K : Type} [Field K]

def RationalExpression.fraction : RationalExpression K→Poly K×Poly K
  | polynomial p => (p,Poly.C 1)
  | add a b => (a.fraction.1*b.fraction.2+b.fraction.1*a.fraction.2,a.fraction.2*b.fraction.2)
  | mul a b => (a.fraction.1*b.fraction.1,a.fraction.2*b.fraction.2)
  | neg a => (-a.fraction.1,a.fraction.2)
  | inv a => (a.fraction.2,a.fraction.1)

def RationalExpression.eval : RationalExpression K→K→K
  | polynomial p,z => p.eval z
  | add a b,z => a.eval z+b.eval z
  | mul a b,z => a.eval z*b.eval z
  | neg a,z => -a.eval z
  | inv a,z => (a.eval z)⁻¹

def RationalExpression.guard : RationalExpression K→Poly K
  | polynomial _ => Poly.C 1
  | add a b => a.guard*b.guard
  | mul a b => a.guard*b.guard
  | neg a => a.guard
  | inv a => a.guard*a.fraction.1

def RationalExpression.SafeAt : RationalExpression K→K→Prop
  | polynomial _,_ => True
  | add a b,z => a.SafeAt z ∧ b.SafeAt z
  | mul a b,z => a.SafeAt z ∧ b.SafeAt z
  | neg a,z => a.SafeAt z
  | inv a,z => a.SafeAt z ∧ a.eval z≠0

/-- Every inverted numerator is formally nonzero. This does not say that it
is nonzero at every challenge; roots are counted by the guard polynomial. -/
def RationalExpression.Regular : RationalExpression K→Prop
  | polynomial _ => True
  | add a b => a.Regular ∧ b.Regular
  | mul a b => a.Regular ∧ b.Regular
  | neg a => a.Regular
  | inv a => a.Regular ∧ ¬a.fraction.1.IsZero

variable {K : Type} [Field K]
private theorem mul_nonzero (a b : K) (ha : a≠0) (hb : b≠0) : a*b≠0 := by
  intro zero
  rcases Field.of_mul_eq_zero zero with h|h
  · exact ha h
  · exact hb h
private theorem split_nonzero (a b : K) (h : a*b≠0) : a≠0 ∧ b≠0 := by
  constructor <;> intro zero <;> apply h <;> rw [zero] <;> grind

/-- The guard suffices both for a nonzero denominator and the exact
cross-multiplied evaluation identity. No inverse is specialized at a pole. -/
theorem rational_specialization_certificate (e : RationalExpression K) (z : K)
    (good : e.guard.eval z≠0) :
    e.fraction.2.eval z≠0 ∧ e.fraction.2.eval z*e.eval z=e.fraction.1.eval z := by
  induction e with
  | polynomial p =>
    simp only [RationalExpression.guard,RationalExpression.fraction,RationalExpression.eval,Poly.eval_C] at good ⊢
    exact ⟨good,by grind⟩
  | add a b ia ib =>
    have guards:=split_nonzero _ _ (show a.guard.eval z*b.guard.eval z≠0 by simpa only [RationalExpression.guard,Poly.eval_mul] using good)
    have ca:=ia guards.1
    have cb:=ib guards.2
    simp only [RationalExpression.fraction,RationalExpression.eval,Poly.eval_add,Poly.eval_mul]
    exact ⟨mul_nonzero _ _ ca.1 cb.1,by grind⟩
  | mul a b ia ib =>
    have guards:=split_nonzero _ _ (show a.guard.eval z*b.guard.eval z≠0 by simpa only [RationalExpression.guard,Poly.eval_mul] using good)
    have ca:=ia guards.1
    have cb:=ib guards.2
    simp only [RationalExpression.fraction,RationalExpression.eval,Poly.eval_mul]
    exact ⟨mul_nonzero _ _ ca.1 cb.1,by grind⟩
  | neg a ia =>
    have ca:=ia good
    simp only [RationalExpression.fraction,RationalExpression.eval,Poly.eval_neg]
    exact ⟨ca.1,by grind⟩
  | inv a ia =>
    have guards:=split_nonzero _ _ (show a.guard.eval z*a.fraction.1.eval z≠0 by simpa only [RationalExpression.guard,Poly.eval_mul] using good)
    have ca:=ia guards.1
    have nz : a.eval z≠0 := by intro zero;apply guards.2;rw [←ca.2,zero];grind
    have inverse:=Field.mul_inv_cancel nz
    simp only [RationalExpression.fraction,RationalExpression.eval]
    exact ⟨guards.2,by grind⟩

/-- The explicit guard records precisely the syntactic division domain,
including poles that algebraic cancellation of the output could conceal. -/
theorem rational_guard_safe_iff (e : RationalExpression K) (z : K) :
    e.guard.eval z≠0 ↔ e.SafeAt z := by
  induction e with
  | polynomial p => simp only [RationalExpression.guard,Poly.eval_C,RationalExpression.SafeAt];exact ⟨fun _=>True.intro,fun _ h=>Field.zero_ne_one h.symm⟩
  | add a b ia ib =>
    simp only [RationalExpression.guard,Poly.eval_mul,RationalExpression.SafeAt]
    exact ⟨fun h=>⟨ia.mp (split_nonzero _ _ h).1,ib.mp (split_nonzero _ _ h).2⟩,
      fun h=>mul_nonzero _ _ (ia.mpr h.1) (ib.mpr h.2)⟩
  | mul a b ia ib =>
    simp only [RationalExpression.guard,Poly.eval_mul,RationalExpression.SafeAt]
    exact ⟨fun h=>⟨ia.mp (split_nonzero _ _ h).1,ib.mp (split_nonzero _ _ h).2⟩,
      fun h=>mul_nonzero _ _ (ia.mpr h.1) (ib.mpr h.2)⟩
  | neg a ia => exact ia
  | inv a ia =>
    simp only [RationalExpression.guard,Poly.eval_mul,RationalExpression.SafeAt]
    constructor
    · intro good
      have parts:=split_nonzero _ _ good
      have cert:=rational_specialization_certificate a z parts.1
      refine ⟨ia.mp parts.1,?_⟩
      intro zero
      apply parts.2
      rw [←cert.2,zero];grind
    · intro safe
      have child:=ia.mpr safe.1
      have cert:=rational_specialization_certificate a z child
      apply mul_nonzero _ _ child
      rw [←cert.2]
      exact mul_nonzero _ _ cert.1 safe.2

/-- Formal regularity ensures a nonzero guard polynomial, not universal safety. -/
theorem rational_regular_guard_nonzero (e : RationalExpression K) (regular : e.Regular) :
    ¬e.guard.IsZero := by
  induction e with
  | polynomial p =>
    intro zero
    have h:=zero 0
    change (1:K)=0 at h
    exact Field.zero_ne_one h.symm
  | add a b ia ib => exact polynomial_product_nonzero _ _ (ia regular.1) (ib regular.2)
  | mul a b ia ib => exact polynomial_product_nonzero _ _ (ia regular.1) (ib regular.2)
  | neg a ia => exact ia regular
  | inv a ia => exact polynomial_product_nonzero _ _ (ia regular.1) regular.2
/-- Rational fraction evaluation is valid on the explicit guarded domain. -/
theorem rational_specialization_eval (e : RationalExpression K) (z : K)
    (good : e.guard.eval z≠0) :
    e.eval z=e.fraction.1.eval z*(e.fraction.2.eval z)⁻¹ := by
  have cert:=rational_specialization_certificate e z good
  have inverse:=Field.mul_inv_cancel cert.1
  grind

/-- Syntactic upper bounds for numerator, denominator and guard degrees.
No cancellation is assumed; repeated inversions can make these bounds large. -/
def rationalDegreeBudget : RationalExpression K→Nat×Nat×Nat
  | .polynomial p => (p.coeffs.length-1,0,0)
  | .add a b =>
    let x:=rationalDegreeBudget a
    let y:=rationalDegreeBudget b
    (max (x.1+y.2.1) (y.1+x.2.1),x.2.1+y.2.1,x.2.2+y.2.2)
  | .mul a b =>
    let x:=rationalDegreeBudget a
    let y:=rationalDegreeBudget b
    (x.1+y.1,x.2.1+y.2.1,x.2.2+y.2.2)
  | .neg a => rationalDegreeBudget a
  | .inv a =>
    let x:=rationalDegreeBudget a
    (x.2.1,x.1,x.2.2+x.1)

/-- The degree budgets are proved for the actual unnormalized polynomials. -/
theorem rational_degree_budgets (e : RationalExpression K) :
    e.fraction.1.DegLt ((rationalDegreeBudget e).1+1) ∧
    e.fraction.2.DegLt ((rationalDegreeBudget e).2.1+1) ∧
    e.guard.DegLt ((rationalDegreeBudget e).2.2+1) := by
  induction e with
  | polynomial p =>
    refine ⟨?_,Poly.degLt_length (Poly.C 1),Poly.degLt_length (Poly.C 1)⟩
    exact Poly.DegLt.mono (Poly.degLt_length p) (by simp only [rationalDegreeBudget];omega)
  | add a b ia ib =>
    simp only [RationalExpression.fraction,RationalExpression.guard,rationalDegreeBudget]
    refine ⟨Poly.degLt_add ?_ ?_,Poly.degLt_mul ia.2.1 ib.2.1,Poly.degLt_mul ia.2.2 ib.2.2⟩
    · exact Poly.DegLt.mono (Poly.degLt_mul ia.1 ib.2.1) (by omega)
    · exact Poly.DegLt.mono (Poly.degLt_mul ib.1 ia.2.1) (by omega)
  | mul a b ia ib => exact ⟨Poly.degLt_mul ia.1 ib.1,Poly.degLt_mul ia.2.1 ib.2.1,Poly.degLt_mul ia.2.2 ib.2.2⟩
  | neg a ia => exact ⟨Poly.degLt_neg ia.1,ia.2.1,ia.2.2⟩
  | inv a ia => exact ⟨ia.2.1,ia.1,Poly.degLt_mul ia.2.2 ia.1⟩

/-- At most guardDegree distinct challenges are excluded by a regular
expression. This is a syntactic-pole bound, not the full MCA exception count. -/
theorem rational_unsafe_specialization_count (e : RationalExpression K)
    (regular : e.Regular) (sample : List K) (distinct : sample.Nodup) :
    count sample (fun z=>¬e.SafeAt z)≤(rationalDegreeBudget e).2.2 := by
  have roots:=PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval K
    e.guard ((rationalDegreeBudget e).2.2+1) sample
    (rational_regular_guard_nonzero e regular) (rational_degree_budgets e).2.2 distinct
  have subset : count sample (fun z=>¬e.SafeAt z)≤count sample (fun z=>e.guard.eval z=0) := by
    apply count_mono
    intro z excluded
    apply Classical.byContradiction
    intro nonzero
    exact excluded ((rational_guard_safe_iff e z).mp nonzero)
  omega
end NearCompression
