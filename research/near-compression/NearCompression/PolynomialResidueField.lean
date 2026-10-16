import NearCompression.PolynomialResidueQuotient

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]
attribute [local instance] Semiring.natCast Ring.intCast

instance residueAdd (h : Poly K) : Add (PolynomialResidue h) := ⟨polynomialResidueAdd h⟩
instance residueMul (h : Poly K) : Mul (PolynomialResidue h) := ⟨polynomialResidueMul h⟩
instance residueNeg (h : Poly K) : Neg (PolynomialResidue h) := ⟨polynomialResidueNeg h⟩
instance residueSub (h : Poly K) : Sub (PolynomialResidue h) := ⟨fun a b=>a+ -b⟩
instance residueOfNat (h : Poly K) (n : Nat) : OfNat (PolynomialResidue h) n :=
  ⟨polynomialResidueClass h (Poly.C (OfNat.ofNat n))⟩
instance residueNatCast (h : Poly K) : NatCast (PolynomialResidue h) :=
  ⟨fun n=>polynomialResidueClass h (Poly.C (Nat.cast n))⟩
instance residueIntCast (h : Poly K) : IntCast (PolynomialResidue h) :=
  ⟨fun n=>polynomialResidueClass h (Poly.C (Int.cast n))⟩
instance residueNSMul (h : Poly K) : SMul Nat (PolynomialResidue h) := ⟨fun n a=>(Nat.cast n)*a⟩
instance residueZSMul (h : Poly K) : SMul Int (PolynomialResidue h) := ⟨fun n a=>(Int.cast n)*a⟩
def residuePower (h : Poly K) (a : PolynomialResidue h) : Nat → PolynomialResidue h
  | 0 => 1
  | n+1 => residuePower h a n*a
instance residuePow (h : Poly K) : HPow (PolynomialResidue h) Nat (PolynomialResidue h) := ⟨residuePower h⟩

private theorem class_equal (h p q : Poly K) (same : PolynomialCoeffEq p q) :
    polynomialResidueClass h p=polynomialResidueClass h q :=
  (polynomial_residue_class_eq_iff h p q).mpr (polynomial_residue_of_coeff_eq h p q same)

private theorem constant_product (c : K) (q : Poly K) (i : Nat) :
    (Poly.C c*q).coeff i=c*q.coeff i := by
  change (Poly.smul c q+Poly.mk [0]).coeff i=_
  rw [Poly.coeff_add,Poly.coeff_smul]
  have zero : (Poly.mk [0] : Poly K).coeff i=0 := by cases i <;> rfl
  rw [zero];grind

private theorem constant_zero (h : Poly K) : polynomialResidueClass h Poly.zero=(0 : PolynomialResidue h) := by
  apply class_equal
  intro i
  cases i <;> rfl

/-- The quotient is a commutative ring for every modulus, including reducible ones. -/
instance polynomialResidueCommRing (h : Poly K) : CommRing (PolynomialResidue h) where
  add_zero := by
    intro a;induction a using Quotient.inductionOn with | h p =>
      apply class_equal;intro i;rw [Poly.coeff_add]
      have zero : (Poly.C (0:K)).coeff i=0 := by cases i <;> rfl
      rw [zero];grind
  add_comm := by
    intro a b;induction a using Quotient.inductionOn with | h p =>
      induction b using Quotient.inductionOn with | h q =>
        apply class_equal;intro i;rw [Poly.coeff_add,Poly.coeff_add];grind
  add_assoc := by
    intro a b c;induction a using Quotient.inductionOn with | h p =>
      induction b using Quotient.inductionOn with | h q =>
        induction c using Quotient.inductionOn with | h r =>
          apply class_equal;intro i;simp only [Poly.coeff_add];grind
  mul_assoc := polynomial_residue_mul_assoc h
  mul_comm := polynomial_residue_mul_comm h
  mul_one := by
    intro a;induction a using Quotient.inductionOn with | h p =>
      apply class_equal;intro i;rw [polynomial_mul_comm,constant_product];grind
  one_mul := by
    intro a;induction a using Quotient.inductionOn with | h p =>
      apply class_equal;intro i;rw [constant_product];grind
  right_distrib := polynomial_residue_add_mul h
  left_distrib := by
    intro a b c;induction a using Quotient.inductionOn with | h p =>
      induction b using Quotient.inductionOn with | h q =>
        induction c using Quotient.inductionOn with | h r =>
          exact class_equal h _ _ (polynomial_mul_add p q r)
  mul_zero := by
    intro a;induction a using Quotient.inductionOn with | h p =>
      apply class_equal;intro i;rw [polynomial_mul_comm,constant_product]
      have zero : (Poly.C (0:K)).coeff i=0 := by cases i <;> rfl
      rw [zero];grind
  zero_mul := by
    intro a;induction a using Quotient.inductionOn with | h p =>
      apply class_equal;intro i;rw [constant_product]
      have zero : (Poly.C (0:K)).coeff i=0 := by cases i <;> rfl
      rw [zero];grind
  pow_zero := fun _=>rfl
  pow_succ := fun _ _=>rfl
  ofNat_succ := by
    intro n;apply class_equal;intro i
    rw [Poly.coeff_add]
    cases i with
    | zero => change (OfNat.ofNat (n+1):K)=OfNat.ofNat n+1;exact Semiring.ofNat_succ n
    | succ i => change (0:K)=0+0;grind
  ofNat_eq_natCast := by
    intro n
    change polynomialResidueClass h (Poly.C (OfNat.ofNat n))=polynomialResidueClass h (Poly.C (Nat.cast n))
    rw [Semiring.ofNat_eq_natCast]
  nsmul_eq_natCast_mul := by intro n a;rfl
  neg_add_cancel := by
    intro a;induction a using Quotient.inductionOn with | h p =>
      apply class_equal;intro i;rw [Poly.coeff_add,Poly.coeff_neg]
      have zero : (Poly.C (0:K)).coeff i=0 := by cases i <;> rfl
      rw [zero];grind
  sub_eq_add_neg := fun _ _=>rfl
  neg_zsmul := by
    intro n a;induction a using Quotient.inductionOn with | h p =>
      apply class_equal;intro i;rw [constant_product,Poly.coeff_neg,constant_product]
      change (Int.cast (-n):K)*p.coeff i= -((Int.cast n:K)*p.coeff i)
      grind
  zsmul_natCast_eq_nsmul := by
    intro n a
    change polynomialResidueClass h (Poly.C (Int.cast (Int.ofNat n)))*a=polynomialResidueClass h (Poly.C (Nat.cast n))*a
    have same : (Int.cast (Int.ofNat n):K)=Nat.cast n := Ring.intCast_natCast n
    rw [same]
  intCast_ofNat := by
    intro n
    change polynomialResidueClass h (Poly.C (Int.cast (Int.ofNat n)))=polynomialResidueClass h (Poly.C (OfNat.ofNat n))
    have same : (Int.cast (Int.ofNat n):K)=OfNat.ofNat n :=
      (Ring.intCast_natCast n).trans (Semiring.ofNat_eq_natCast n).symm
    rw [same]
  intCast_neg := by
    intro n;apply class_equal;intro i;rw [Poly.coeff_neg]
    cases i with
    | zero => change (Int.cast (-n):K)= -(Int.cast n:K);grind
    | succ i => change (0:K)= -0;grind

/-- Classical inverse selection on quotient elements, with zero mapped to zero. -/
noncomputable def polynomialResidueInv (h : Poly K) (irreducible : PolynomialIrreducible h)
    (a : PolynomialResidue h) : PolynomialResidue h := by
  classical
  exact if nz : a≠polynomialResidueClass h Poly.zero then
    Classical.choose (polynomial_residue_quotient_inverse h irreducible a nz) else 0

/-- A field structure constructed from the irreducible modulus, not assumed. -/
@[instance_reducible] noncomputable def polynomialResidueField (h : Poly K) (irreducible : PolynomialIrreducible h) :
    Field (PolynomialResidue h) := by
  letI : Inv (PolynomialResidue h) := ⟨polynomialResidueInv h irreducible⟩
  apply Field.ofInv
  · intro same
    exact polynomial_residue_one_ne_zero h irreducible (same.symm.trans (constant_zero h).symm)
  · change polynomialResidueInv h irreducible 0=0
    simp [polynomialResidueInv,constant_zero]
  · intro a nz
    have nonzero : a≠polynomialResidueClass h Poly.zero := by rwa [constant_zero]
    change a*polynomialResidueInv h irreducible a=1
    rw [polynomialResidueInv,dite_eq_left nonzero,CommSemiring.mul_comm]
    exact Classical.choose_spec (polynomial_residue_quotient_inverse h irreducible a nonzero)

/-- Audit entry covering every field axiom and the chosen inverse construction. -/
theorem polynomial_residue_field_exists (h : Poly K) (irreducible : PolynomialIrreducible h) :
    Nonempty (Field (PolynomialResidue h)) := ⟨polynomialResidueField h irreducible⟩

/-- The canonical unital map from the coefficient field into its root extension. -/
noncomputable def polynomialResidueEmbedding (h : Poly K) (irreducible : PolynomialIrreducible h) :
    letI := polynomialResidueField h irreducible
    PolynomialFieldMap K (PolynomialResidue h) := by
  letI := polynomialResidueField h irreducible
  exact {
    toFun := fun c=>polynomialResidueClass h (Poly.C c)
    zero := rfl
    one := rfl
    add := by
      intro a b;apply class_equal;intro i;rw [Poly.coeff_add]
      cases i with | zero => rfl | succ i => change (0:K)=0+0;grind
    mul := by
      intro a b;apply class_equal;intro i;rw [constant_product]
      cases i with | zero => rfl | succ i => change (0:K)=a*0;grind }

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

/-- Evaluating a transported polynomial at the class of X recovers its class. -/
theorem polynomial_residue_eval_variable (h : Poly K) (irreducible : PolynomialIrreducible h)
    (p : Poly K) :
    letI := polynomialResidueField h irreducible
    (transportPolynomial (polynomialResidueEmbedding h irreducible) p).eval
      (polynomialResidueClass h Poly.X)=polynomialResidueClass h p := by
  letI := polynomialResidueField h irreducible
  cases p with | mk cs =>
    induction cs with
    | nil => exact (constant_zero h).symm
    | cons c cs ih =>
      change polynomialResidueClass h (Poly.C c)+polynomialResidueClass h Poly.X*
        (transportPolynomial (polynomialResidueEmbedding h irreducible) (Poly.mk cs)).eval
          (polynomialResidueClass h Poly.X)=polynomialResidueClass h (Poly.mk (c::cs))
      rw [ih]
      exact class_equal h _ _ (cons_reconstruction c cs)

/-- The constructed extension actually contains a root of the mapped modulus. -/
theorem polynomial_residue_modulus_root (h : Poly K) (irreducible : PolynomialIrreducible h) :
    letI := polynomialResidueField h irreducible
    (transportPolynomial (polynomialResidueEmbedding h irreducible) h).eval
      (polynomialResidueClass h Poly.X)=0 := by
  letI := polynomialResidueField h irreducible
  rw [polynomial_residue_eval_variable]
  have divides : PolynomialDivides h h := by
    refine ⟨Poly.C 1,?_⟩;intro i;rw [constant_product];grind
  exact ((polynomial_residue_zero_iff h h).mpr divides).trans (constant_zero h)

/-- The root just constructed is smooth under the existing degree budget. -/
theorem polynomial_residue_modulus_smooth (characteristic : Nat) [IsCharP K characteristic]
    (h : Poly K) (irreducible : PolynomialIrreducible h) (d : Nat)
    (degree : h.DegLt (d+1)) (leading : h.coeff d≠0)
    (positive : 0<d) (small : d<characteristic) :
    letI := polynomialResidueField h irreducible
    (polynomialDerivative (transportPolynomial (polynomialResidueEmbedding h irreducible) h)).eval
      (polynomialResidueClass h Poly.X)≠0 := by
  letI := polynomialResidueField h irreducible
  exact irreducible_extension_root_smooth (polynomialResidueEmbedding h irreducible)
    characteristic h d irreducible degree leading positive small _ (polynomial_residue_modulus_root h irreducible)

/-- The coefficient map is injective, so the quotient really extends K. -/
theorem polynomial_residue_embedding_injective (h : Poly K) (irreducible : PolynomialIrreducible h)
    (a b : K) (same : polynomialResidueClass h (Poly.C a)=
      polynomialResidueClass h (Poly.C b)) : a=b := by
  obtain ⟨d,_,_,hd,leading,_⟩:=polynomial_division_exists Poly.zero h irreducible.1
  have positive : 0<d := by
    cases d with | zero => exact False.elim (irreducible.2.1 hd) | succ d => omega
  have equal:=polynomial_reduced_residue_unique h (Poly.C a) (Poly.C b) d leading
    (Poly.DegLt.mono (Poly.degLt_length _) positive)
    (Poly.DegLt.mono (Poly.degLt_length _) positive)
    ((polynomial_residue_class_eq_iff h _ _).mp same)
  exact equal 0

/-- Every nonzero nonconstant polynomial has a root in a constructed field
extension, using the proved existence of an irreducible divisor. -/
theorem polynomial_root_extension_exists (p : Poly K) (nonzero : ¬p.IsZero)
    (nonconstant : ¬p.DegLt 1) :
    ∃ h : Poly K, ∃ irreducible : PolynomialIrreducible h,
      letI := polynomialResidueField h irreducible
      (transportPolynomial (polynomialResidueEmbedding h irreducible) p).eval
        (polynomialResidueClass h Poly.X)=0 := by
  obtain ⟨h,irreducible,divides⟩:=polynomial_irreducible_divisor_exists p nonzero nonconstant
  refine ⟨h,irreducible,?_⟩
  letI := polynomialResidueField h irreducible
  rw [polynomial_residue_eval_variable]
  exact ((polynomial_residue_zero_iff h p).mpr divides).trans (constant_zero h)
end NearCompression
