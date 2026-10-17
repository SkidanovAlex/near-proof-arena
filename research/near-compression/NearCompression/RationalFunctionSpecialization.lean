import NearCompression.PolynomialRationalField
import NearCompression.RationalSpecialization

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

private theorem coefficient_equal_eval (p q : Poly K) (same : PolynomialCoeffEq p q) (z : K) :
    p.eval z=q.eval z := by
  have zero : (p-q).IsZero := by intro i;rw [Poly.coeff_sub,same i];grind
  have entry:=Poly.eval_of_isZero zero z
  rw [Poly.eval_sub] at entry
  grind

/-- Evaluation descends to formal polynomials, before forming fractions. -/
def formalPolynomialEval (z : K) : FormalPolynomial K → K :=
  Quotient.lift (fun p=>p.eval z) (fun p q same=>
    coefficient_equal_eval p q ((formal_polynomial_eq_iff p q).mp
      (Quotient.sound (s:=polynomialResidueSetoid Poly.zero) same)) z)

theorem formal_polynomial_eval_add (a b : FormalPolynomial K) (z : K) :
    formalPolynomialEval z (a+b)=formalPolynomialEval z a+formalPolynomialEval z b := by
  induction a using Quotient.inductionOn with | h p =>
    induction b using Quotient.inductionOn with | h q => exact Poly.eval_add p q z

theorem formal_polynomial_eval_mul (a b : FormalPolynomial K) (z : K) :
    formalPolynomialEval z (a*b)=formalPolynomialEval z a*formalPolynomialEval z b := by
  induction a using Quotient.inductionOn with | h p =>
    induction b using Quotient.inductionOn with | h q => exact Poly.eval_mul p q z

def PolynomialFraction.SafeAt (a : PolynomialFraction K) (z : K) : Prop :=
  formalPolynomialEval z a.denominator≠0

def PolynomialFraction.valueAt (a : PolynomialFraction K) (z : K) : K :=
  formalPolynomialEval z a.numerator*(formalPolynomialEval z a.denominator)⁻¹

/-- Equivalent fractions agree wherever both representatives are safe. -/
theorem polynomial_fraction_safe_value_eq (a b : PolynomialFraction K) (z : K)
    (same : a.Equivalent b) (sa : a.SafeAt z) (sb : b.SafeAt z) : a.valueAt z=b.valueAt z := by
  have entry:=congrArg (formalPolynomialEval z) same
  rw [formal_polynomial_eval_mul,formal_polynomial_eval_mul] at entry
  have ia:=Field.mul_inv_cancel sa
  have ib:=Field.mul_inv_cancel sb
  unfold PolynomialFraction.valueAt
  grind

/-- Partial specialization: a value is witnessed by some safe representative.
No evaluation is assigned at a pole by totalized field inversion. -/
def PolynomialRationalValueAt (r : PolynomialRational K) (z value : K) : Prop :=
  ∃ a : PolynomialFraction K, polynomialRationalClass a=r ∧ a.SafeAt z ∧ a.valueAt z=value

/-- Specialization is unique even when witnessed by different representatives. -/
theorem polynomial_rational_value_unique (r : PolynomialRational K) (z a b : K)
    (ha : PolynomialRationalValueAt r z a) (hb : PolynomialRationalValueAt r z b) : a=b := by
  obtain ⟨ra,ea,sa,va⟩:=ha
  obtain ⟨rb,eb,sb,vb⟩:=hb
  have same:=(polynomial_rational_class_eq_iff ra rb).mp (ea.trans eb.symm)
  exact va.symm.trans ((polynomial_fraction_safe_value_eq ra rb z same sa sb).trans vb)

private theorem mul_nonzero (a b : K) (ha : a≠0) (hb : b≠0) : a*b≠0 := by
  intro zero
  rcases Field.of_mul_eq_zero zero with zero|zero
  · exact ha zero
  · exact hb zero

theorem polynomial_rational_value_add (r s : PolynomialRational K) (z a b : K)
    (ha : PolynomialRationalValueAt r z a) (hb : PolynomialRationalValueAt s z b) :
    PolynomialRationalValueAt (r+s) z (a+b) := by
  obtain ⟨ra,ea,sa,va⟩:=ha
  obtain ⟨rb,eb,sb,vb⟩:=hb
  refine ⟨ra.add rb,?_,?_,?_⟩
  · change polynomialRationalClass ra+polynomialRationalClass rb=r+s
    rw [ea,eb]
  · change formalPolynomialEval z (ra.denominator*rb.denominator)≠0
    rw [formal_polynomial_eval_mul];exact mul_nonzero _ _ sa sb
  · have ia:=Field.mul_inv_cancel sa
    have ib:=Field.mul_inv_cancel sb
    have prod:=Field.mul_inv_cancel (mul_nonzero _ _ sa sb)
    unfold PolynomialFraction.valueAt at *
    change formalPolynomialEval z (ra.numerator*rb.denominator+rb.numerator*ra.denominator)*
      (formalPolynomialEval z (ra.denominator*rb.denominator))⁻¹=a+b
    rw [formal_polynomial_eval_add,formal_polynomial_eval_mul,formal_polynomial_eval_mul,formal_polynomial_eval_mul]
    grind

theorem polynomial_rational_value_mul (r s : PolynomialRational K) (z a b : K)
    (ha : PolynomialRationalValueAt r z a) (hb : PolynomialRationalValueAt s z b) :
    PolynomialRationalValueAt (r*s) z (a*b) := by
  obtain ⟨ra,ea,sa,va⟩:=ha
  obtain ⟨rb,eb,sb,vb⟩:=hb
  refine ⟨ra.mul rb,?_,?_,?_⟩
  · change polynomialRationalClass ra*polynomialRationalClass rb=r*s
    rw [ea,eb]
  · change formalPolynomialEval z (ra.denominator*rb.denominator)≠0
    rw [formal_polynomial_eval_mul];exact mul_nonzero _ _ sa sb
  · have ia:=Field.mul_inv_cancel sa
    have ib:=Field.mul_inv_cancel sb
    have prod:=Field.mul_inv_cancel (mul_nonzero _ _ sa sb)
    unfold PolynomialFraction.valueAt at *
    change formalPolynomialEval z (ra.numerator*rb.numerator)*
      (formalPolynomialEval z (ra.denominator*rb.denominator))⁻¹=a*b
    rw [formal_polynomial_eval_mul,formal_polynomial_eval_mul]
    grind

/-- Formal regularity suffices to construct an actual fraction representative. -/
theorem rational_regular_denominator_nonzero (e : RationalExpression K) (regular : e.Regular) :
    ¬e.fraction.2.IsZero := by
  induction e with
  | polynomial p => intro zero;exact Field.zero_ne_one (zero 0).symm
  | add a b ia ib => exact polynomial_product_nonzero _ _ (ia regular.1) (ib regular.2)
  | mul a b ia ib => exact polynomial_product_nonzero _ _ (ia regular.1) (ib regular.2)
  | neg a ia => exact ia regular
  | inv a ia => exact regular.2

def rationalExpressionFraction (e : RationalExpression K) (regular : e.Regular) : PolynomialFraction K :=
  ⟨formalPolynomial e.fraction.1,formalPolynomial e.fraction.2,
    fun zero=>rational_regular_denominator_nonzero e regular ((formal_polynomial_zero_iff _).mp zero)⟩

def rationalExpressionFunction (e : RationalExpression K) (regular : e.Regular) : PolynomialRational K :=
  polynomialRationalClass (rationalExpressionFraction e regular)

/-- Existing guarded expression evaluation agrees with the constructed
rational function on the original syntactic safe domain. -/
theorem rational_expression_function_specializes (e : RationalExpression K) (regular : e.Regular)
    (z : K) (safe : e.SafeAt z) :
    PolynomialRationalValueAt (rationalExpressionFunction e regular) z (e.eval z) := by
  have cert:=rational_specialization_certificate e z ((rational_guard_safe_iff e z).mpr safe)
  refine ⟨rationalExpressionFraction e regular,rfl,cert.1,?_⟩
  change e.fraction.1.eval z*(e.fraction.2.eval z)⁻¹=e.eval z
  have inverse:=Field.mul_inv_cancel cert.1
  grind

/-- Formal rational-function identities specialize when both original
expressions are safe, retaining poles hidden by cancellation. -/
theorem rational_expression_identity_specializes (e f : RationalExpression K)
    (er : e.Regular) (fr : f.Regular)
    (identity : rationalExpressionFunction e er=rationalExpressionFunction f fr)
    (z : K) (es : e.SafeAt z) (fs : f.SafeAt z) : e.eval z=f.eval z := by
  have left:=rational_expression_function_specializes e er z es
  rw [identity] at left
  exact polynomial_rational_value_unique _ z _ _ left (rational_expression_function_specializes f fr z fs)

/-- Safe reciprocal specialization requires a nonzero specialized value,
not merely a formally nonzero rational function. -/
theorem polynomial_rational_value_inv (r : PolynomialRational K) (z value : K)
    (specialization : PolynomialRationalValueAt r z value) (nonzero : value≠0) :
    PolynomialRationalValueAt r⁻¹ z value⁻¹ := by
  obtain ⟨a,eq,safe,eval⟩:=specialization
  have numerator : formalPolynomialEval z a.numerator≠0 := by
    intro zero
    apply nonzero
    unfold PolynomialFraction.valueAt at eval
    rw [zero] at eval
    grind
  have formal : a.numerator≠0 := by
    intro zero;apply numerator;rw [zero];change (Poly.C (0:K)).eval z=0;exact Poly.eval_C 0 z
  let b : PolynomialFraction K := ⟨a.denominator,a.numerator,formal⟩
  refine ⟨b,?_,numerator,?_⟩
  · rw [←eq]
    change polynomialRationalClass b=polynomialRationalClass a.inv
    rw [PolynomialFraction.inv,dite_eq_left formal]
  · have di:=Field.mul_inv_cancel safe
    have ni:=Field.mul_inv_cancel numerator
    have vi:=Field.mul_inv_cancel nonzero
    unfold PolynomialFraction.valueAt at eval
    change formalPolynomialEval z a.denominator*(formalPolynomialEval z a.numerator)⁻¹=value⁻¹
    grind

/-- Formal identities fail under totalized expression evaluation only inside
the union of the two syntactic pole sets. This is not the full MCA exception set. -/
theorem rational_expression_identity_exception_count (e f : RationalExpression K)
    (er : e.Regular) (fr : f.Regular)
    (identity : rationalExpressionFunction e er=rationalExpressionFunction f fr)
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun z=>e.eval z≠f.eval z)≤
      (rationalDegreeBudget e).2.2+(rationalDegreeBudget f).2.2 := by
  have bound:=rational_unsafe_specialization_count (.add e f) ⟨er,fr⟩ sample distinct
  have subset : count sample (fun z=>e.eval z≠f.eval z)≤
      count sample (fun z=>¬(RationalExpression.add e f).SafeAt z) := by
    apply count_mono
    intro z different safe
    exact different (rational_expression_identity_specializes e f er fr identity z safe.1 safe.2)
  exact Nat.le_trans subset bound
end NearCompression
