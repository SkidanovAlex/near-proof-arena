import NearCompression.AlgebraicGuardedInverse

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {F K : Type} [Field F] [Field K]

/-- Arithmetic properties needed for specialization of a finite Hensel lift.
No total function or unconditional inverse preservation is assumed. -/
structure PartialRingRelation (F K : Type) [Field F] [Field K] where
  relates : F→K→Prop
  zero : relates 0 0
  one : relates 1 1
  negOne : relates (-1) (-1)
  add : ∀ {x y a b},relates x a → relates y b → relates (x+y) (a+b)
  mul : ∀ {x y a b},relates x a → relates y b → relates (x*y) (a*b)

def RelatedPolynomial (R : PartialRingRelation F K) (p : Poly F) (q : Poly K) : Prop :=
  ∀ i,R.relates (p.coeff i) (q.coeff i)

inductive RelatedPolynomialRows (R : PartialRingRelation F K) : List (Poly F)→List (Poly K)→Prop
  | nil : RelatedPolynomialRows R [] []
  | cons {p q ps qs} : RelatedPolynomial R p q → RelatedPolynomialRows R ps qs → RelatedPolynomialRows R (p::ps) (q::qs)

private theorem related_dot (R : PartialRingRelation F K) (xs : List Nat)
    (a b : Nat→F) (c d : Nat→K) (ha : ∀ i,R.relates (a i) (c i))
    (hb : ∀ i,R.relates (b i) (d i)) : R.relates (kernelDot xs a b) (kernelDot xs c d) := by
  induction xs with
  | nil => exact R.zero
  | cons i xs ih => exact R.add (R.mul (ha i) (hb i)) ih

theorem related_polynomial_add (R : PartialRingRelation F K) (p q : Poly F) (u v : Poly K)
    (hp : RelatedPolynomial R p u) (hq : RelatedPolynomial R q v) : RelatedPolynomial R (p+q) (u+v) := by
  intro i;rw [Poly.coeff_add,Poly.coeff_add];exact R.add (hp i) (hq i)

theorem related_polynomial_mul (R : PartialRingRelation F K) (p q : Poly F) (u v : Poly K)
    (hp : RelatedPolynomial R p u) (hq : RelatedPolynomial R q v) : RelatedPolynomial R (p*q) (u*v) := by
  intro i
  let n:=max p.coeffs.length u.coeffs.length
  rw [polynomial_bounded_product_coefficient p q n i (Poly.DegLt.mono (Poly.degLt_length p) (Nat.le_max_left _ _)),
    polynomial_bounded_product_coefficient u v n i (Poly.DegLt.mono (Poly.degLt_length u) (Nat.le_max_right _ _))]
  apply related_dot R _ _ _ _ _ hp
  intro j
  by_cases inside : j≤i
  · simp only [ite_eq_left inside];exact hq _
  · simp only [ite_eq_right inside];exact R.zero

theorem related_bivariate_substitute (R : PartialRingRelation F K) (rows : List (Poly F))
    (numeric : List (Poly K)) (f : Poly F) (g : Poly K)
    (inputs : RelatedPolynomialRows R rows numeric) (curve : RelatedPolynomial R f g) :
    RelatedPolynomial R (bivariateSubstitute rows f) (bivariateSubstitute numeric g) := by
  induction inputs with
  | nil => exact fun _=>R.zero
  | cons head tail ih => exact related_polynomial_add R _ _ _ _ head (related_polynomial_mul R _ _ _ _ curve ih)

/-- The recurrence preserves the initial coefficient even before root or
smoothness assumptions are supplied. -/
theorem hensel_lift_constant_unconditional (rows : List (Poly F)) (a : F) (n : Nat) :
    (curveHenselLift rows a n).coeff 0=a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (curveHenselLift rows a n+Poly.smul _ (jetMonomial (n+1))).coeff 0=a
    rw [Poly.coeff_add,Poly.coeff_smul,jet_monomial_coefficient,ite_eq_right (by omega),ih]
    grind

/-- A single related initial slope inverse suffices for all finite Hensel
steps: the operational slope depends only on the unchanged constant term. -/
theorem partial_hensel_lift_specializes (R : PartialRingRelation F K)
    (rows : List (Poly F)) (numeric : List (Poly K)) (a : F) (b : K)
    (inputs : RelatedPolynomialRows R rows numeric) (initial : R.relates a b)
    (inverse : R.relates (curveHenselSlope rows (Poly.C a))⁻¹
      (curveHenselSlope numeric (Poly.C b))⁻¹) (n : Nat) :
    RelatedPolynomial R (curveHenselLift rows a n) (curveHenselLift numeric b n) := by
  induction n with
  | zero => intro i;cases i with | zero => exact initial | succ i => exact R.zero
  | succ n ih =>
    have residual:=related_bivariate_substitute R rows numeric _ _ inputs ih (n+1)
    have negResidual : R.relates (-(bivariateSubstitute rows (curveHenselLift rows a n)).coeff (n+1))
        (-(bivariateSubstitute numeric (curveHenselLift numeric b n)).coeff (n+1)) := by
      have h:=R.mul R.negOne residual
      have left : (-1:F)*(bivariateSubstitute rows (curveHenselLift rows a n)).coeff (n+1)=
          -(bivariateSubstitute rows (curveHenselLift rows a n)).coeff (n+1) := by grind
      have right : (-1:K)*(bivariateSubstitute numeric (curveHenselLift numeric b n)).coeff (n+1)=
          -(bivariateSubstitute numeric (curveHenselLift numeric b n)).coeff (n+1) := by grind
      rwa [left,right] at h
    have inverses : R.relates (curveHenselSlope rows (curveHenselLift rows a n))⁻¹
        (curveHenselSlope numeric (curveHenselLift numeric b n))⁻¹ := by
      rw [hensel_slope_constant_congr rows _ (Poly.C a) (hensel_lift_constant_unconditional rows a n),
        hensel_slope_constant_congr numeric _ (Poly.C b) (hensel_lift_constant_unconditional numeric b n)]
      exact inverse
    have correction:=R.mul negResidual inverses
    apply related_polynomial_add R _ _ _ _ ih
    intro i
    rw [Poly.coeff_smul,Poly.coeff_smul]
    apply R.mul correction
    rw [jet_monomial_coefficient,jet_monomial_coefficient]
    by_cases equal : i=n+1
    · simp only [ite_eq_left equal];exact R.one
    · simp only [ite_eq_right equal];exact R.zero
/-- Base-field constants have regular algebraic representatives everywhere. -/
theorem algebraic_residue_base_constant (h : Poly (PolynomialRational K)) (c z a : K) :
    AlgebraicResidueValueAt h (polynomialResidueClass h (Poly.C (polynomialRationalCoefficientMap.toFun c))) z a c := by
  refine ⟨Poly.C (polynomialRationalCoefficientMap.toFun c),Poly.C c,rfl,?_,Poly.eval_C c a⟩
  exact .cons (rational_coefficient_specializes c z) .nil

/-- The proved partial algebraic specialization supplies the arithmetic
relation required by the recurrence theorem. -/
noncomputable def algebraicResiduePartialRelation (h : Poly (PolynomialRational K))
    (irreducible : PolynomialIrreducible h) (z a : K) :
    letI := polynomialResidueField h irreducible
    PartialRingRelation (PolynomialResidue h) K := by
  letI := polynomialResidueField h irreducible
  refine ⟨(fun x value=>AlgebraicResidueValueAt h x z a value),
    algebraic_residue_base_constant h 0 z a,algebraic_residue_base_constant h 1 z a,?_,?_,?_⟩
  · have hneg:=algebraic_residue_base_constant h (-1) z a
    have scalar : (polynomialRationalCoefficientMap (K:=K)).toFun (-1)= -1 := by
      have h:=(polynomialRationalCoefficientMap (K:=K)).add (-1) 1
      have zero : (-1:K)+1=0 := by grind
      rw [zero,polynomialRationalCoefficientMap.zero,polynomialRationalCoefficientMap.one] at h
      grind
    have classNeg : polynomialResidueClass h (Poly.C (polynomialRationalCoefficientMap.toFun (-1)))=
        (-1 : PolynomialResidue h) := by
      change polynomialResidueClass h (Poly.C (polynomialRationalCoefficientMap.toFun (-1)))=
        polynomialResidueClass h (-(Poly.C 1))
      apply (polynomial_residue_class_eq_iff _ _ _).mpr
      apply polynomial_residue_of_coeff_eq
      intro i
      rw [Poly.coeff_neg]
      cases i with
      | zero => exact scalar
      | succ i => change (0:PolynomialRational K)= -0;grind
    rwa [classNeg] at hneg
  · intro x y u v hx hy
    exact algebraic_residue_value_add h x y z a u v hx hy
  · intro x y u v hx hy
    exact algebraic_residue_value_mul h x y z a u v hx hy

/-- Every coefficient of the actual algebraic Hensel lift specializes to the
numeric lift once the source coefficients, initial root, and guarded initial
slope inverse specialize. No inverse assumption is repeated at later steps. -/
theorem algebraic_hensel_lift_specializes (h : Poly (PolynomialRational K))
    (irreducible : PolynomialIrreducible h) (z a : K) :
    letI := polynomialResidueField h irreducible
    ∀ (rows : List (Poly (PolynomialResidue h))) (numeric : List (Poly K))
      (initial : PolynomialResidue h),
      RelatedPolynomialRows (algebraicResiduePartialRelation h irreducible z a) rows numeric →
      AlgebraicResidueValueAt h initial z a a →
      AlgebraicResidueValueAt h (curveHenselSlope rows (Poly.C initial))⁻¹ z a
        (curveHenselSlope numeric (Poly.C a))⁻¹ →
      ∀ n i,AlgebraicResidueValueAt h ((curveHenselLift rows initial n).coeff i) z a
        ((curveHenselLift numeric a n).coeff i) := by
  letI := polynomialResidueField h irreducible
  intro rows numeric initial inputs root inverse n i
  exact partial_hensel_lift_specializes (algebraicResiduePartialRelation h irreducible z a)
    rows numeric initial a inputs root inverse n i
end NearCompression
