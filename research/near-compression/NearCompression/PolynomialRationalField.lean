import NearCompression.PolynomialFractions

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]
attribute [local instance] Semiring.natCast Ring.intCast

instance rationalAdd : Add (PolynomialRational K) := ⟨polynomialRationalAdd⟩
instance rationalMul : Mul (PolynomialRational K) := ⟨polynomialRationalMul⟩
instance rationalNeg : Neg (PolynomialRational K) := ⟨polynomialRationalNeg⟩
instance rationalSub : Sub (PolynomialRational K) := ⟨fun a b=>a+ -b⟩
instance rationalOfNat (n : Nat) : OfNat (PolynomialRational K) n :=
  ⟨polynomialRationalClass (.ofPolynomial (OfNat.ofNat n))⟩
instance rationalNatCast : NatCast (PolynomialRational K) :=
  ⟨fun n=>polynomialRationalClass (.ofPolynomial (Nat.cast n))⟩
instance rationalIntCast : IntCast (PolynomialRational K) :=
  ⟨fun n=>polynomialRationalClass (.ofPolynomial (Int.cast n))⟩
instance rationalNSMul : SMul Nat (PolynomialRational K) := ⟨fun n a=>(Nat.cast n)*a⟩
instance rationalZSMul : SMul Int (PolynomialRational K) := ⟨fun n a=>(Int.cast n)*a⟩
def rationalPower (a : PolynomialRational K) : Nat → PolynomialRational K
  | 0 => 1
  | n+1 => rationalPower a n*a
instance rationalPow : HPow (PolynomialRational K) Nat (PolynomialRational K) := ⟨rationalPower⟩

/-- All ring laws descend through formal fraction equivalence. -/
instance polynomialRationalCommRing : CommRing (PolynomialRational K) where
  add_zero := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      apply (polynomial_rational_class_eq_iff _ _).mpr
      dsimp [PolynomialFraction.Equivalent,PolynomialFraction.add,PolynomialFraction.mul,PolynomialFraction.neg,PolynomialFraction.ofPolynomial]
      grind
  add_comm := by
    intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        apply (polynomial_rational_class_eq_iff _ _).mpr
        dsimp [PolynomialFraction.Equivalent,PolynomialFraction.add,PolynomialFraction.mul,PolynomialFraction.neg,PolynomialFraction.ofPolynomial]
        grind
  add_assoc := by
    intro a b c
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        induction c using Quotient.inductionOn with | h c =>
          apply (polynomial_rational_class_eq_iff _ _).mpr
          dsimp [PolynomialFraction.Equivalent,PolynomialFraction.add,PolynomialFraction.mul,PolynomialFraction.neg,PolynomialFraction.ofPolynomial]
          grind
  mul_assoc := by
    intro a b c
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        induction c using Quotient.inductionOn with | h c =>
          apply (polynomial_rational_class_eq_iff _ _).mpr
          dsimp [PolynomialFraction.Equivalent,PolynomialFraction.add,PolynomialFraction.mul,PolynomialFraction.neg,PolynomialFraction.ofPolynomial]
          grind
  mul_comm := by
    intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        apply (polynomial_rational_class_eq_iff _ _).mpr
        dsimp [PolynomialFraction.Equivalent,PolynomialFraction.add,PolynomialFraction.mul,PolynomialFraction.neg,PolynomialFraction.ofPolynomial]
        grind
  mul_one := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      apply (polynomial_rational_class_eq_iff _ _).mpr
      dsimp [PolynomialFraction.Equivalent,PolynomialFraction.add,PolynomialFraction.mul,PolynomialFraction.neg,PolynomialFraction.ofPolynomial]
      grind
  one_mul := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      apply (polynomial_rational_class_eq_iff _ _).mpr
      dsimp [PolynomialFraction.Equivalent,PolynomialFraction.add,PolynomialFraction.mul,PolynomialFraction.neg,PolynomialFraction.ofPolynomial]
      grind
  left_distrib := by
    intro a b c
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        induction c using Quotient.inductionOn with | h c =>
          apply (polynomial_rational_class_eq_iff _ _).mpr
          dsimp [PolynomialFraction.Equivalent,PolynomialFraction.add,PolynomialFraction.mul,PolynomialFraction.neg,PolynomialFraction.ofPolynomial]
          grind
  right_distrib := by
    intro a b c
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        induction c using Quotient.inductionOn with | h c =>
          apply (polynomial_rational_class_eq_iff _ _).mpr
          dsimp [PolynomialFraction.Equivalent,PolynomialFraction.add,PolynomialFraction.mul,PolynomialFraction.neg,PolynomialFraction.ofPolynomial]
          grind
  zero_mul := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      apply (polynomial_rational_class_eq_iff _ _).mpr
      dsimp [PolynomialFraction.Equivalent,PolynomialFraction.add,PolynomialFraction.mul,PolynomialFraction.neg,PolynomialFraction.ofPolynomial]
      grind
  mul_zero := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      apply (polynomial_rational_class_eq_iff _ _).mpr
      dsimp [PolynomialFraction.Equivalent,PolynomialFraction.add,PolynomialFraction.mul,PolynomialFraction.neg,PolynomialFraction.ofPolynomial]
      grind
  neg_add_cancel := by
    intro a
    induction a using Quotient.inductionOn with | h a =>
      apply (polynomial_rational_class_eq_iff _ _).mpr
      dsimp [PolynomialFraction.Equivalent,PolynomialFraction.add,PolynomialFraction.mul,PolynomialFraction.neg,PolynomialFraction.ofPolynomial]
      grind
  pow_zero := fun _=>rfl
  pow_succ := fun _ _=>rfl
  sub_eq_add_neg := fun _ _=>rfl
  ofNat_succ := by
    intro n
    apply (polynomial_rational_class_eq_iff _ _).mpr
    change (OfNat.ofNat (n+1) : FormalPolynomial K)*(1*1)=(OfNat.ofNat n*1+1*1)*1
    have h:=Semiring.ofNat_succ (α:=FormalPolynomial K) n
    grind
  ofNat_eq_natCast := by
    intro n
    change polynomialRationalClass (.ofPolynomial (OfNat.ofNat n : FormalPolynomial K))=polynomialRationalClass (.ofPolynomial (Nat.cast n))
    rw [Semiring.ofNat_eq_natCast]
  nsmul_eq_natCast_mul := fun _ _=>rfl
  neg_zsmul := by
    intro n a
    induction a using Quotient.inductionOn with | h a =>
      apply (polynomial_rational_class_eq_iff _ _).mpr
      change ((Int.cast (-n):FormalPolynomial K)*a.numerator)*(1*a.denominator)=
        -((Int.cast n:FormalPolynomial K)*a.numerator)*(1*a.denominator)
      rw [Ring.intCast_neg]
      grind
  zsmul_natCast_eq_nsmul := by
    intro n a
    change polynomialRationalClass (.ofPolynomial (Int.cast (Int.ofNat n):FormalPolynomial K))*a=
      polynomialRationalClass (.ofPolynomial (Nat.cast n))*a
    have same : (Int.cast (Int.ofNat n):FormalPolynomial K)=Nat.cast n := Ring.intCast_natCast n
    rw [same]
  intCast_ofNat := by
    intro n
    change polynomialRationalClass (.ofPolynomial (Int.cast (Int.ofNat n):FormalPolynomial K))=
      polynomialRationalClass (.ofPolynomial (OfNat.ofNat n))
    have same : (Int.cast (Int.ofNat n):FormalPolynomial K)=OfNat.ofNat n :=
      (Ring.intCast_natCast n).trans (Semiring.ofNat_eq_natCast n).symm
    rw [same]
  intCast_neg := by
    intro n
    apply (polynomial_rational_class_eq_iff _ _).mpr
    change (Int.cast (-n):FormalPolynomial K)*1= -(Int.cast n:FormalPolynomial K)*1
    rw [Ring.intCast_neg]

noncomputable instance rationalInv : Inv (PolynomialRational K) := ⟨polynomialRationalInv⟩

/-- Constructed rational-function field, using formal rather than sampled equality. -/
noncomputable instance polynomialRationalField : Field (PolynomialRational K) :=
  Field.ofInv
    (fun same=>formal_polynomial_one_nonzero
      (polynomial_rational_polynomial_injective _ _ same.symm))
    polynomial_rational_inv_zero
    (fun nonzero=>polynomial_rational_mul_inverse _ nonzero)

/-- Audit closure includes every constructed field axiom. -/
theorem polynomial_rational_field_exists : Nonempty (Field (PolynomialRational K)) :=
  ⟨polynomialRationalField⟩

def polynomialRationalOfPolynomial (p : Poly K) : PolynomialRational K :=
  polynomialRationalClass (.ofPolynomial (formalPolynomial p))

theorem polynomial_rational_of_polynomial_add (p q : Poly K) :
    polynomialRationalOfPolynomial (p+q)=polynomialRationalOfPolynomial p+polynomialRationalOfPolynomial q := by
  apply (polynomial_rational_class_eq_iff _ _).mpr
  change (formalPolynomial p+formalPolynomial q)*(1*1)=
    (formalPolynomial p*1+formalPolynomial q*1)*1
  grind

theorem polynomial_rational_of_polynomial_mul (p q : Poly K) :
    polynomialRationalOfPolynomial (p*q)=polynomialRationalOfPolynomial p*polynomialRationalOfPolynomial q := by
  apply (polynomial_rational_class_eq_iff _ _).mpr
  change (formalPolynomial p*formalPolynomial q)*(1*1)=(formalPolynomial p*formalPolynomial q)*1
  grind

theorem polynomial_rational_of_polynomial_eq_iff (p q : Poly K) :
    polynomialRationalOfPolynomial p=polynomialRationalOfPolynomial q ↔ PolynomialCoeffEq p q := by
  constructor
  · intro eq
    exact (formal_polynomial_eq_iff p q).mp (polynomial_rational_polynomial_injective _ _ eq)
  · intro eq
    have same:=(formal_polynomial_eq_iff p q).mpr eq
    exact congrArg (fun a=>polynomialRationalClass (.ofPolynomial a)) same

/-- Canonical embedding of the base field into rational functions. -/
def polynomialRationalCoefficientMap : PolynomialFieldMap K (PolynomialRational K) where
  toFun c := polynomialRationalOfPolynomial (Poly.C c)
  zero := rfl
  one := rfl
  add a b := by
    rw [←polynomial_rational_of_polynomial_add]
    apply (polynomial_rational_of_polynomial_eq_iff _ _).mpr
    intro i;rw [Poly.coeff_add]
    cases i with | zero => rfl | succ i => change (0:K)=0+0;grind
  mul a b := by
    rw [←polynomial_rational_of_polynomial_mul]
    apply (polynomial_rational_of_polynomial_eq_iff _ _).mpr
    intro i
    change (Poly.C (a*b)).coeff i=(Poly.smul a (Poly.C b)+Poly.mk [0]).coeff i
    rw [Poly.coeff_add,Poly.coeff_smul]
    cases i with | zero => change a*b=a*b+0;grind | succ i => change (0:K)=a*0+0;grind

theorem polynomial_rational_coefficient_injective (a b : K)
    (same : polynomialRationalCoefficientMap.toFun a=polynomialRationalCoefficientMap.toFun b) : a=b :=
  (polynomial_rational_of_polynomial_eq_iff _ _).mp same 0

/-- The characteristic budget is preserved by the constructed coefficient field. -/
instance polynomialRationalCharacteristic (characteristic : Nat) [IsCharP K characteristic] :
    IsCharP (PolynomialRational K) characteristic :=
  IsCharP.mk' _ _ (ofNat_eq_zero_iff := fun n=>by
    constructor
    · intro zero
      have base : (OfNat.ofNat n : K)=0 := polynomial_rational_coefficient_injective _ _ zero
      exact (IsCharP.ofNat_eq_zero_iff characteristic n).mp base
    · intro modular
      have base : (OfNat.ofNat n : K)=0 := (IsCharP.ofNat_eq_zero_iff characteristic n).mpr modular
      change polynomialRationalOfPolynomial (Poly.C (OfNat.ofNat n : K))=polynomialRationalOfPolynomial (Poly.C 0)
      rw [base])

/-- Audit entry includes the inherited characteristic construction. -/
theorem polynomial_rational_characteristic_preserved (characteristic : Nat) [IsCharP K characteristic]
    (n : Nat) : (OfNat.ofNat n : PolynomialRational K)=0 ↔ n%characteristic=0 :=
  IsCharP.ofNat_eq_zero_iff characteristic n

private theorem cons_reconstruction (c : K) (cs : List K) :
    PolynomialCoeffEq (Poly.C c+Poly.X*Poly.mk cs) (Poly.mk (c::cs)) := by
  intro i
  rw [Poly.coeff_add]
  have shift : (Poly.X*Poly.mk cs).coeff i=if i<1 then 0 else (Poly.mk cs).coeff (i-1) :=
    polynomial_monomial_mul_coefficient (Poly.mk cs) 1 i
  rw [shift]
  cases i with
  | zero => change c+0=c;grind
  | succ i =>
    simp only [Nat.add_sub_cancel]
    change 0+(Poly.mk cs).coeff i=(Poly.mk cs).coeff i
    grind

/-- Evaluation at the rational indeterminate preserves the entire formal polynomial. -/
theorem polynomial_rational_eval_variable (p : Poly K) :
    (transportPolynomial polynomialRationalCoefficientMap p).eval
      (polynomialRationalOfPolynomial Poly.X)=polynomialRationalOfPolynomial p := by
  cases p with | mk cs =>
    induction cs with
    | nil =>
      apply (polynomial_rational_of_polynomial_eq_iff _ _).mpr
      intro i;cases i <;> rfl
    | cons c cs ih =>
      change polynomialRationalOfPolynomial (Poly.C c)+polynomialRationalOfPolynomial Poly.X*
        (transportPolynomial polynomialRationalCoefficientMap (Poly.mk cs)).eval
          (polynomialRationalOfPolynomial Poly.X)=polynomialRationalOfPolynomial (Poly.mk (c::cs))
      rw [ih,←polynomial_rational_of_polynomial_mul,←polynomial_rational_of_polynomial_add]
      exact (polynomial_rational_of_polynomial_eq_iff _ _).mpr (cons_reconstruction c cs)

/-- The indeterminate is transcendental over the base field; finite-field
vanishing functions never collapse formally nonzero polynomials. -/
theorem polynomial_rational_variable_transcendental (p : Poly K) (nonzero : ¬p.IsZero) :
    (transportPolynomial polynomialRationalCoefficientMap p).eval
      (polynomialRationalOfPolynomial Poly.X)≠0 := by
  rw [polynomial_rational_eval_variable]
  intro zero
  apply nonzero
  have formal:=polynomial_rational_polynomial_injective _ _ zero
  exact (formal_polynomial_zero_iff p).mp formal
end NearCompression
