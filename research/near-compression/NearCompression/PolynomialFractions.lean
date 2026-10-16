import NearCompression.PolynomialResidueField

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Formal polynomials modulo coefficient equality, with the proved ring structure. -/
abbrev FormalPolynomial (K : Type) [Field K] := PolynomialResidue (Poly.zero : Poly K)

def formalPolynomial (p : Poly K) : FormalPolynomial K := polynomialResidueClass Poly.zero p

/-- Quotient by the zero modulus identifies precisely coefficient-equal polynomials. -/
theorem formal_polynomial_eq_iff (p q : Poly K) :
    formalPolynomial p=formalPolynomial q ↔ PolynomialCoeffEq p q := by
  constructor
  · intro equal
    obtain ⟨s,eq⟩:=(polynomial_residue_class_eq_iff Poly.zero p q).mp equal
    have zero : (s*Poly.zero).IsZero := (polynomial_product_zero_iff s Poly.zero).mpr
      (Or.inr (fun _=>rfl))
    intro i
    have entry:=eq i
    rw [Poly.coeff_sub,zero i] at entry
    grind
  · intro equal
    exact (polynomial_residue_class_eq_iff Poly.zero p q).mpr
      (polynomial_residue_of_coeff_eq Poly.zero p q equal)

theorem formal_polynomial_zero_iff (p : Poly K) : formalPolynomial p=0 ↔ p.IsZero := by
  change formalPolynomial p=formalPolynomial (Poly.C 0) ↔ _
  rw [formal_polynomial_eq_iff]
  have zero : ∀ i,(Poly.C (0:K)).coeff i=0 := by intro i;cases i <;> rfl
  constructor
  · intro eq i;rw [eq i,zero i]
  · intro eq i;rw [eq i,zero i]

/-- Integral-domain property survives the coefficient quotient. -/
theorem formal_polynomial_mul_zero (p q : FormalPolynomial K) (zero : p*q=0) : p=0 ∨ q=0 := by
  induction p using Quotient.inductionOn with | h a =>
    induction q using Quotient.inductionOn with | h b =>
      have product : (a*b).IsZero := (formal_polynomial_zero_iff (a*b)).mp zero
      rcases (polynomial_product_zero_iff a b).mp product with az|bz
      · exact Or.inl ((formal_polynomial_zero_iff a).mpr az)
      · exact Or.inr ((formal_polynomial_zero_iff b).mpr bz)

theorem formal_polynomial_one_nonzero : (1 : FormalPolynomial K)≠0 := by
  intro zero
  have impossible:=(formal_polynomial_zero_iff (Poly.C (1:K))).mp zero 0
  exact Field.zero_ne_one impossible.symm

private theorem product_nonzero (a b : FormalPolynomial K) (an : a≠0) (bn : b≠0) : a*b≠0 := by
  intro zero
  rcases formal_polynomial_mul_zero a b zero with a|b
  · exact an a
  · exact bn b

/-- Cancellation for formal polynomials, without evaluating at sampled points. -/
theorem formal_polynomial_cancel (a b c : FormalPolynomial K) (cn : c≠0)
    (same : a*c=b*c) : a=b := by
  have zero : (a-b)*c=0 := by grind
  rcases formal_polynomial_mul_zero (a-b) c zero with ab|c0
  · grind
  · exact False.elim (cn c0)

/-- A polynomial fraction has a formally nonzero denominator, which may still
vanish at some or all base-field evaluation points. -/
structure PolynomialFraction (K : Type) [Field K] where
  numerator : FormalPolynomial K
  denominator : FormalPolynomial K
  denominator_nonzero : denominator≠0

def PolynomialFraction.Equivalent (a b : PolynomialFraction K) : Prop :=
  a.numerator*b.denominator=b.numerator*a.denominator

def PolynomialFraction.add (a b : PolynomialFraction K) : PolynomialFraction K :=
  ⟨a.numerator*b.denominator+b.numerator*a.denominator,a.denominator*b.denominator,
    product_nonzero _ _ a.denominator_nonzero b.denominator_nonzero⟩

def PolynomialFraction.mul (a b : PolynomialFraction K) : PolynomialFraction K :=
  ⟨a.numerator*b.numerator,a.denominator*b.denominator,
    product_nonzero _ _ a.denominator_nonzero b.denominator_nonzero⟩

def PolynomialFraction.neg (a : PolynomialFraction K) : PolynomialFraction K :=
  ⟨-a.numerator,a.denominator,a.denominator_nonzero⟩

def PolynomialFraction.ofPolynomial (p : FormalPolynomial K) : PolynomialFraction K :=
  ⟨p,1,formal_polynomial_one_nonzero⟩

theorem polynomial_fraction_refl (a : PolynomialFraction K) : a.Equivalent a := rfl

theorem polynomial_fraction_symm (a b : PolynomialFraction K) (same : a.Equivalent b) : b.Equivalent a := same.symm

/-- Transitivity uses the nonzero middle denominator; it is not assumed. -/
theorem polynomial_fraction_trans (a b c : PolynomialFraction K)
    (ab : a.Equivalent b) (bc : b.Equivalent c) : a.Equivalent c := by
  unfold PolynomialFraction.Equivalent at *
  apply formal_polynomial_cancel _ _ b.denominator b.denominator_nonzero
  grind

theorem polynomial_fraction_add_congr (a a' b b' : PolynomialFraction K)
    (aa : a.Equivalent a') (bb : b.Equivalent b') : (a.add b).Equivalent (a'.add b') := by
  unfold PolynomialFraction.Equivalent PolynomialFraction.add at *
  simp only []
  grind

theorem polynomial_fraction_mul_congr (a a' b b' : PolynomialFraction K)
    (aa : a.Equivalent a') (bb : b.Equivalent b') : (a.mul b).Equivalent (a'.mul b') := by
  unfold PolynomialFraction.Equivalent PolynomialFraction.mul at *
  simp only []
  grind

theorem polynomial_fraction_neg_congr (a b : PolynomialFraction K)
    (same : a.Equivalent b) : a.neg.Equivalent b.neg := by
  unfold PolynomialFraction.Equivalent PolynomialFraction.neg at *
  simp only []
  grind

def polynomialFractionSetoid (K : Type) [Field K] : Setoid (PolynomialFraction K) where
  r := PolynomialFraction.Equivalent
  iseqv := ⟨polynomial_fraction_refl,fun eq=>polynomial_fraction_symm _ _ eq,
    fun eq₁ eq₂=>polynomial_fraction_trans _ _ _ eq₁ eq₂⟩

/-- Rational functions as fractions modulo formal cross multiplication. -/
abbrev PolynomialRational (K : Type) [Field K] := Quotient (polynomialFractionSetoid K)

def polynomialRationalClass (a : PolynomialFraction K) : PolynomialRational K := Quotient.mk _ a

def polynomialRationalAdd : PolynomialRational K → PolynomialRational K → PolynomialRational K :=
  Quotient.lift₂ (fun a b=>polynomialRationalClass (a.add b))
    (fun _ _ _ _ aa bb=>Quotient.sound (polynomial_fraction_add_congr _ _ _ _ aa bb))

def polynomialRationalMul : PolynomialRational K → PolynomialRational K → PolynomialRational K :=
  Quotient.lift₂ (fun a b=>polynomialRationalClass (a.mul b))
    (fun _ _ _ _ aa bb=>Quotient.sound (polynomial_fraction_mul_congr _ _ _ _ aa bb))

def polynomialRationalNeg : PolynomialRational K → PolynomialRational K :=
  Quotient.lift (fun a=>polynomialRationalClass a.neg)
    (fun _ _ eq=>Quotient.sound (polynomial_fraction_neg_congr _ _ eq))

theorem polynomial_rational_class_eq_iff (a b : PolynomialFraction K) :
    polynomialRationalClass a=polynomialRationalClass b ↔ a.Equivalent b :=
  ⟨fun eq=>Quotient.exact eq,fun eq=>Quotient.sound (s:=polynomialFractionSetoid K) eq⟩

/-- Embedding formal polynomials as denominator-one fractions is injective. -/
theorem polynomial_rational_polynomial_injective (p q : FormalPolynomial K)
    (same : polynomialRationalClass (.ofPolynomial p)=polynomialRationalClass (.ofPolynomial q)) : p=q := by
  have eq:=(polynomial_rational_class_eq_iff _ _).mp same
  change p*1=q*1 at eq
  grind

/-- The zero fraction is detected by its numerator, independently of denominator. -/
theorem polynomial_fraction_zero_iff (a : PolynomialFraction K) :
    a.Equivalent (.ofPolynomial 0) ↔ a.numerator=0 := by
  change a.numerator*1=0*a.denominator ↔ a.numerator=0
  grind

private theorem numerator_zero_congr (a b : PolynomialFraction K) (same : a.Equivalent b) :
    a.numerator=0 ↔ b.numerator=0 := by
  constructor
  · intro az
    have zero : b.numerator*a.denominator=0 := by
      change a.numerator*b.denominator=b.numerator*a.denominator at same
      grind
    rcases formal_polynomial_mul_zero _ _ zero with bz|bad
    · exact bz
    · exact False.elim (a.denominator_nonzero bad)
  · intro bz
    have zero : a.numerator*b.denominator=0 := by
      change a.numerator*b.denominator=b.numerator*a.denominator at same
      grind
    rcases formal_polynomial_mul_zero _ _ zero with az|bad
    · exact az
    · exact False.elim (b.denominator_nonzero bad)

noncomputable def PolynomialFraction.inv (a : PolynomialFraction K) : PolynomialFraction K := by
  classical
  exact if nz : a.numerator≠0 then ⟨a.denominator,a.numerator,nz⟩ else .ofPolynomial 0

/-- Reciprocal is well-defined even for alternative representations of zero. -/
theorem polynomial_fraction_inv_congr (a b : PolynomialFraction K) (same : a.Equivalent b) :
    a.inv.Equivalent b.inv := by
  classical
  by_cases az : a.numerator=0
  · have bz:=(numerator_zero_congr a b same).mp az
    simp only [PolynomialFraction.inv,az,bz,ne_eq,not_true_eq_false,dite_false]
    exact polynomial_fraction_refl _
  · have bz : b.numerator≠0 := fun zero=>az ((numerator_zero_congr a b same).mpr zero)
    simp only [PolynomialFraction.inv,dite_eq_left az,dite_eq_left bz]
    change a.denominator*b.numerator=b.denominator*a.numerator
    change a.numerator*b.denominator=b.numerator*a.denominator at same
    grind

noncomputable def polynomialRationalInv : PolynomialRational K → PolynomialRational K :=
  Quotient.lift (fun a=>polynomialRationalClass a.inv)
    (fun _ _ eq=>Quotient.sound (polynomial_fraction_inv_congr _ _ eq))

/-- Every nonzero rational function has its actual swapped-fraction inverse. -/
theorem polynomial_rational_mul_inverse (a : PolynomialRational K)
    (nonzero : a≠polynomialRationalClass (.ofPolynomial 0)) :
    polynomialRationalMul a (polynomialRationalInv a)=polynomialRationalClass (.ofPolynomial 1) := by
  induction a using Quotient.inductionOn with | h a =>
    have nz : a.numerator≠0 := by
      intro zero
      exact nonzero ((polynomial_rational_class_eq_iff _ _).mpr ((polynomial_fraction_zero_iff a).mpr zero))
    apply (polynomial_rational_class_eq_iff _ _).mpr
    change (a.mul a.inv).Equivalent (.ofPolynomial 1)
    rw [PolynomialFraction.inv,dite_eq_left nz]
    change (a.numerator*a.denominator)*1=1*(a.denominator*a.numerator)
    grind

theorem polynomial_rational_inv_zero :
    polynomialRationalInv (polynomialRationalClass (.ofPolynomial (0 : FormalPolynomial K)))=
      polynomialRationalClass (.ofPolynomial 0) := by
  change polynomialRationalClass (PolynomialFraction.ofPolynomial (0:FormalPolynomial K)).inv=_
  simp [PolynomialFraction.inv,PolynomialFraction.ofPolynomial]
end NearCompression
