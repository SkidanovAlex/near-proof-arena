import NearCompression.AlgebraicRootSpecialization

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Explicit polynomial numerator and nonzero denominator for a coefficient. -/
structure RationalCoefficientPresentation (K : Type) [Field K] where
  numerator : Poly K
  denominator : Poly K
  denominator_nonzero : ¬denominator.IsZero

def RationalCoefficientPresentation.fraction (a : RationalCoefficientPresentation K) : PolynomialFraction K :=
  ⟨formalPolynomial a.numerator,formalPolynomial a.denominator,
    fun zero=>a.denominator_nonzero ((formal_polynomial_zero_iff _).mp zero)⟩

def RationalCoefficientPresentation.value (a : RationalCoefficientPresentation K) : PolynomialRational K :=
  polynomialRationalClass a.fraction

def RationalCoefficientPresentation.eval (a : RationalCoefficientPresentation K) (z : K) : K :=
  a.numerator.eval z*(a.denominator.eval z)⁻¹

/-- Polynomial representatives exist for every coefficient of the actual
rational-function quotient, not only for preselected expression syntax. -/
theorem rational_coefficient_presentation_exists (r : PolynomialRational K) :
    ∃ a : RationalCoefficientPresentation K,a.value=r := by
  induction r using Quotient.inductionOn with | h a =>
    cases a with | mk numerator denominator nonzero =>
      induction numerator using Quotient.inductionOn with | h n =>
        induction denominator using Quotient.inductionOn with | h d =>
          have dn : ¬d.IsZero := fun zero=>nonzero ((formal_polynomial_zero_iff d).mpr zero)
          exact ⟨⟨n,d,dn⟩,rfl⟩

def presentedRationalPolynomial (cs : List (RationalCoefficientPresentation K)) : Poly (PolynomialRational K) :=
  Poly.mk (cs.map RationalCoefficientPresentation.value)

def specializePresentedPolynomial (cs : List (RationalCoefficientPresentation K)) (z : K) : Poly K :=
  Poly.mk (cs.map (fun c=>c.eval z))

def coefficientDenominatorGuard : List (RationalCoefficientPresentation K) → Poly K
  | [] => Poly.C 1
  | c::cs => c.denominator*coefficientDenominatorGuard cs

def coefficientDenominatorBudget : List (RationalCoefficientPresentation K) → Nat
  | [] => 0
  | c::cs => (c.denominator.coeffs.length-1)+coefficientDenominatorBudget cs

/-- Every polynomial over rational functions admits a finite explicit presentation. -/
theorem rational_polynomial_presentation_exists (p : Poly (PolynomialRational K)) :
    ∃ cs : List (RationalCoefficientPresentation K),presentedRationalPolynomial cs=p := by
  cases p with | mk ps =>
    induction ps with
    | nil => exact ⟨[],rfl⟩
    | cons r rs ih =>
      obtain ⟨a,ar⟩:=rational_coefficient_presentation_exists r
      obtain ⟨cs,cs_eq⟩:=ih
      refine ⟨a::cs,?_⟩
      have lists:=congrArg Poly.coeffs cs_eq
      change Poly.mk (a.value::cs.map RationalCoefficientPresentation.value)=Poly.mk (r::rs)
      change cs.map RationalCoefficientPresentation.value=rs at lists
      rw [ar,lists]

theorem coefficient_denominator_guard_nonzero (cs : List (RationalCoefficientPresentation K)) :
    ¬(coefficientDenominatorGuard cs).IsZero := by
  induction cs with
  | nil => intro zero;exact Field.zero_ne_one (zero 0).symm
  | cons c cs ih => exact polynomial_product_nonzero _ _ c.denominator_nonzero ih

theorem coefficient_denominator_guard_degree (cs : List (RationalCoefficientPresentation K)) :
    (coefficientDenominatorGuard cs).DegLt (coefficientDenominatorBudget cs+1) := by
  induction cs with
  | nil => exact Poly.degLt_length (Poly.C 1)
  | cons c cs ih =>
    exact Poly.degLt_mul (Poly.DegLt.mono (Poly.degLt_length c.denominator) (by omega)) ih

/-- The single guard supplies all coefficient-specialization witnesses. -/
theorem coefficient_denominator_guard_specializes (cs : List (RationalCoefficientPresentation K))
    (z : K) (good : (coefficientDenominatorGuard cs).eval z≠0) :
    RationalPolynomialSpecializes (presentedRationalPolynomial cs) (specializePresentedPolynomial cs z) z := by
  induction cs with
  | nil => exact .nil
  | cons c cs ih =>
    simp only [coefficientDenominatorGuard,Poly.eval_mul] at good
    have cn : c.denominator.eval z≠0 := by intro zero;apply good;rw [zero];grind
    have tail : (coefficientDenominatorGuard cs).eval z≠0 := by intro zero;apply good;rw [zero];grind
    exact .cons ⟨c.fraction,rfl,cn,rfl⟩ (ih tail)

/-- Actual guard roots, hence all unsafe coefficient specializations, have
an explicit presentation-dependent degree budget on distinct samples. -/
theorem coefficient_denominator_guard_root_count (cs : List (RationalCoefficientPresentation K))
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun z=>(coefficientDenominatorGuard cs).eval z=0)≤coefficientDenominatorBudget cs := by
  have bound:=PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval K
    (coefficientDenominatorGuard cs) (coefficientDenominatorBudget cs+1) sample
    (coefficient_denominator_guard_nonzero cs) (coefficient_denominator_guard_degree cs) distinct
  omega

private theorem guard_append (a b : List (RationalCoefficientPresentation K)) (z : K) :
    (coefficientDenominatorGuard (a++b)).eval z=
      (coefficientDenominatorGuard a).eval z*(coefficientDenominatorGuard b).eval z := by
  induction a with
  | nil => simp only [List.nil_append,coefficientDenominatorGuard,Poly.eval_C];grind
  | cons c cs ih =>
    simp only [List.cons_append,coefficientDenominatorGuard,Poly.eval_mul,ih]
    grind

/-- A concrete shared guard for a polynomial and its Bezout certificate
makes every specialized root smooth outside the guard's roots. -/
theorem presented_bezout_guard_smooth
    (ps aspec bspec : List (RationalCoefficientPresentation K))
    (certificate : PolynomialCoeffEq
      (presentedRationalPolynomial aspec*presentedRationalPolynomial ps+
       presentedRationalPolynomial bspec*polynomialDerivative (presentedRationalPolynomial ps)) (Poly.C 1))
    (z a : K) (good : (coefficientDenominatorGuard (ps++aspec++bspec)).eval z≠0)
    (root : (specializePresentedPolynomial ps z).eval a=0) :
    (polynomialDerivative (specializePresentedPolynomial ps z)).eval a≠0 := by
  rw [guard_append,guard_append] at good
  have pn : (coefficientDenominatorGuard ps).eval z≠0 := by intro zero;apply good;rw [zero];grind
  have an : (coefficientDenominatorGuard aspec).eval z≠0 := by intro zero;apply good;rw [zero];grind
  have bn : (coefficientDenominatorGuard bspec).eval z≠0 := by intro zero;apply good;rw [zero];grind
  exact rational_bezout_specialized_root_smooth _ _ _ _ _ _ z a certificate
    (coefficient_denominator_guard_specializes ps z pn)
    (coefficient_denominator_guard_specializes aspec z an)
    (coefficient_denominator_guard_specializes bspec z bn) root

/-- All singular specialized roots lie in the constructed shared guard set. -/
theorem presented_bezout_singular_count
    (ps aspec bspec : List (RationalCoefficientPresentation K))
    (certificate : PolynomialCoeffEq
      (presentedRationalPolynomial aspec*presentedRationalPolynomial ps+
       presentedRationalPolynomial bspec*polynomialDerivative (presentedRationalPolynomial ps)) (Poly.C 1))
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun z=>∃ a : K, (specializePresentedPolynomial ps z).eval a=0 ∧
      (polynomialDerivative (specializePresentedPolynomial ps z)).eval a=0)≤
      coefficientDenominatorBudget (ps++aspec++bspec) := by
  apply Nat.le_trans _ (coefficient_denominator_guard_root_count (ps++aspec++bspec) sample distinct)
  apply count_mono
  intro z bad
  obtain ⟨a,root,singular⟩:=bad
  apply Classical.byContradiction
  intro good
  exact presented_bezout_guard_smooth ps aspec bspec certificate z a good root singular

/-- Generic irreducibility yields an actual finite guard, certificate
presentations and a singular-point budget. Its degree is presentation-dependent;
no bound in terms of the original interpolation dimensions is asserted. -/
theorem irreducible_specialization_guard_exists (characteristic : Nat) [IsCharP K characteristic]
    (p : Poly (PolynomialRational K)) (d : Nat) (irreducible : PolynomialIrreducible p)
    (degree : p.DegLt (d+1)) (leading : p.coeff d≠0)
    (positive : 0<d) (small : d<characteristic) :
    ∃ ps aspec bspec : List (RationalCoefficientPresentation K),
      presentedRationalPolynomial ps=p ∧
      ¬(coefficientDenominatorGuard (ps++aspec++bspec)).IsZero ∧
      ∀ sample : List K, sample.Nodup →
        count sample (fun z=>∃ a : K, (specializePresentedPolynomial ps z).eval a=0 ∧
          (polynomialDerivative (specializePresentedPolynomial ps z)).eval a=0)≤
          coefficientDenominatorBudget (ps++aspec++bspec) := by
  obtain ⟨A,B,certificate⟩:=irreducible_derivative_bezout characteristic p d irreducible degree leading positive small
  obtain ⟨ps,pe⟩:=rational_polynomial_presentation_exists p
  obtain ⟨aspec,ae⟩:=rational_polynomial_presentation_exists A
  obtain ⟨bspec,be⟩:=rational_polynomial_presentation_exists B
  refine ⟨ps,aspec,bspec,pe,coefficient_denominator_guard_nonzero _,?_⟩
  intro sample distinct
  apply presented_bezout_singular_count ps aspec bspec _ sample distinct
  rwa [pe,ae,be]
end NearCompression
