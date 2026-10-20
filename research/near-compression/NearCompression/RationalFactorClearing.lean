import NearCompression.SelectedSourceSlopeGuard

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Multiplying a presented rational coefficient by its denominator recovers
its formal polynomial numerator, independently of evaluation points. -/
theorem rational_coefficient_denominator_identity (c : RationalCoefficientPresentation K) :
    polynomialRationalOfPolynomial c.denominator*c.value=polynomialRationalOfPolynomial c.numerator := by
  change polynomialRationalClass ((PolynomialFraction.ofPolynomial (formalPolynomial c.denominator)).mul c.fraction)=
    polynomialRationalClass (PolynomialFraction.ofPolynomial (formalPolynomial c.numerator))
  apply (polynomial_rational_class_eq_iff _ _).mpr
  change (formalPolynomial c.denominator*formalPolynomial c.numerator)*1=
    formalPolynomial c.numerator*(1*formalPolynomial c.denominator)
  grind

/-- Explicit common-denominator clearing; each entry is a polynomial in the
parameter. No cancellation or primitive normalization is claimed here. -/
def clearedRationalCoefficientRows : List (RationalCoefficientPresentation K)→List (Poly K)
  | [] => []
  | c::cs => c.numerator*coefficientDenominatorGuard cs ::
      (clearedRationalCoefficientRows cs).map (fun p=>c.denominator*p)

private theorem cleared_map (cs : List (RationalCoefficientPresentation K)) :
    (clearedRationalCoefficientRows cs).map polynomialRationalOfPolynomial=
      cs.map (fun c=>polynomialRationalOfPolynomial (coefficientDenominatorGuard cs)*c.value) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [clearedRationalCoefficientRows,List.map_cons,List.map_map,Function.comp_def,
      coefficientDenominatorGuard,polynomial_rational_of_polynomial_mul]
    have tail : ((clearedRationalCoefficientRows cs).map (fun p=>c.denominator*p)).map polynomialRationalOfPolynomial=
        cs.map (fun d=>(polynomialRationalOfPolynomial c.denominator*
          polynomialRationalOfPolynomial (coefficientDenominatorGuard cs))*d.value) := by
      have mapped:=congrArg (List.map (fun r=>polynomialRationalOfPolynomial c.denominator*r)) ih
      simp only [List.map_map,Function.comp_def] at mapped
      have same : (fun d : RationalCoefficientPresentation K=>
          polynomialRationalOfPolynomial c.denominator*(polynomialRationalOfPolynomial (coefficientDenominatorGuard cs)*d.value))=
          (fun d=>(polynomialRationalOfPolynomial c.denominator*polynomialRationalOfPolynomial (coefficientDenominatorGuard cs))*d.value) := by
        funext d;grind
      rw [same] at mapped
      simpa only [List.map_map,Function.comp_def,polynomial_rational_of_polynomial_mul] using mapped
    congr 1
    · have identity:=rational_coefficient_denominator_identity c
      grind
    · simpa only [List.map_map,Function.comp_def,polynomial_rational_of_polynomial_mul] using tail

/-- Clearing produces precisely a nonzero-scalar multiple of the original
rational polynomial, with coefficient positions and zero padding preserved. -/
theorem rational_polynomial_cleared_identity (cs : List (RationalCoefficientPresentation K)) :
    polynomialParameterFamily (clearedRationalCoefficientRows cs)=
      Poly.smul (polynomialRationalOfPolynomial (coefficientDenominatorGuard cs)) (presentedRationalPolynomial cs) := by
  unfold polynomialParameterFamily
  rw [cleared_map]
  simp [Poly.smul,Poly.scaleL,presentedRationalPolynomial,List.map_map,Function.comp_def]

theorem rational_polynomial_clearing_scalar_nonzero (cs : List (RationalCoefficientPresentation K)) :
    polynomialRationalOfPolynomial (coefficientDenominatorGuard cs)≠0 := by
  intro zero
  have formal:=polynomial_rational_polynomial_injective _ _ zero
  exact coefficient_denominator_guard_nonzero cs ((formal_polynomial_zero_iff _).mp formal)

/-- Every rational-function polynomial has a polynomial-parameter multiple
by an explicit formally nonzero polynomial. Source-degree bounds require
additional normalization and are not inferred from this existence theorem. -/
theorem rational_polynomial_clearing_exists (p : Poly (PolynomialRational K)) :
    ∃ rows : List (Poly K),∃ denominator : Poly K,¬denominator.IsZero ∧
      polynomialParameterFamily rows=Poly.smul (polynomialRationalOfPolynomial denominator) p := by
  obtain ⟨cs,equal⟩:=rational_polynomial_presentation_exists p
  refine ⟨clearedRationalCoefficientRows cs,coefficientDenominatorGuard cs,
    coefficient_denominator_guard_nonzero cs,?_⟩
  rw [rational_polynomial_cleared_identity,equal]

/-- Nonzero scalar clearing preserves every algebraic-variable degree bound. -/
theorem rational_polynomial_cleared_degree_iff (cs : List (RationalCoefficientPresentation K)) (D : Nat) :
    (polynomialParameterFamily (clearedRationalCoefficientRows cs)).DegLt D ↔
      (presentedRationalPolynomial cs).DegLt D := by
  rw [rational_polynomial_cleared_identity]
  constructor
  · intro degree i hi
    have zero:=degree i hi
    rw [Poly.coeff_smul] at zero
    rcases Field.of_mul_eq_zero zero with left|right
    · exact False.elim (rational_polynomial_clearing_scalar_nonzero cs left)
    · exact right
  · exact Poly.degLt_smul _

/-- Clearing changes neither the generic roots nor nonzeroness of the
polynomial over K(Z), because its scalar is formally nonzero. -/
theorem rational_polynomial_cleared_root_iff (cs : List (RationalCoefficientPresentation K))
    (a : PolynomialRational K) :
    (polynomialParameterFamily (clearedRationalCoefficientRows cs)).eval a=0 ↔
      (presentedRationalPolynomial cs).eval a=0 := by
  rw [rational_polynomial_cleared_identity,Poly.eval_smul]
  constructor
  · intro zero
    rcases Field.of_mul_eq_zero zero with left|right
    · exact False.elim (rational_polynomial_clearing_scalar_nonzero cs left)
    · exact right
  · intro zero;rw [zero];grind
private theorem constant_product (c : K) (p : Poly K) (i : Nat) :
    (Poly.C c*p).coeff i=c*p.coeff i := by
  change (Poly.smul c p+Poly.mk [0]).coeff i=_
  rw [Poly.coeff_add,Poly.coeff_smul]
  have zero : (Poly.mk [0] : Poly K).coeff i=0 := by cases i <;> rfl
  rw [zero];grind

private theorem scale_product (c : K) (p q : Poly K) (i : Nat) :
    (Poly.smul c p*q).coeff i=c*(p*q).coeff i := by
  have same : PolynomialCoeffEq (Poly.C c*p) (Poly.smul c p) := by
    intro j;rw [constant_product,Poly.coeff_smul]
  rw [←polynomial_mul_congr _ _ q q same (fun _=>rfl) i,polynomial_mul_assoc,constant_product]

/-- Scaling by a nonzero field element preserves irreducibility. -/
theorem polynomial_nonzero_scalar_irreducible (p : Poly K) (c : K)
    (nonzero : c≠0) (irreducible : PolynomialIrreducible p) : PolynomialIrreducible (Poly.smul c p) := by
  have cancel : ∀ x : K,c*x=0 → x=0 := by
    intro x zero
    rcases Field.of_mul_eq_zero zero with left|right
    · exact False.elim (nonzero left)
    · exact right
  have inverse:=Field.mul_inv_cancel nonzero
  refine ⟨?_,?_,?_⟩
  · intro zero;apply irreducible.1;intro i;apply cancel;simpa only [Poly.coeff_smul] using zero i
  · intro degree;apply irreducible.2.1;intro i hi;apply cancel;simpa only [Poly.coeff_smul] using degree i hi
  · intro a b factorization
    have unscaled : PolynomialCoeffEq p (Poly.smul c⁻¹ a*b) := by
      intro i
      have entry:=factorization i
      rw [Poly.coeff_smul] at entry
      rw [scale_product]
      grind
    rcases irreducible.2.2 (Poly.smul c⁻¹ a) b unscaled with ad|bd
    · left
      intro i hi
      have zero:=ad i hi
      rw [Poly.coeff_smul] at zero
      grind
    · exact Or.inr bd

/-- The cleared polynomial is a valid irreducible modulus over K(Z) whenever
the original rational polynomial was irreducible. -/
theorem rational_polynomial_cleared_irreducible (cs : List (RationalCoefficientPresentation K))
    (irreducible : PolynomialIrreducible (presentedRationalPolynomial cs)) :
    PolynomialIrreducible (polynomialParameterFamily (clearedRationalCoefficientRows cs)) := by
  rw [rational_polynomial_cleared_identity]
  exact polynomial_nonzero_scalar_irreducible _ _ (rational_polynomial_clearing_scalar_nonzero cs) irreducible
end NearCompression
