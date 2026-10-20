import NearCompression.IrreducibleResidueInverse

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Formal coefficient equality always implies congruence modulo any modulus. -/
theorem polynomial_residue_of_coeff_eq (h p q : Poly K) (same : PolynomialCoeffEq p q) :
    PolynomialResidueEq h p q := by
  refine ⟨Poly.zero,?_⟩
  intro i
  rw [Poly.coeff_sub,same i]
  change q.coeff i-q.coeff i=0
  grind

theorem polynomial_residue_refl (h p : Poly K) : PolynomialResidueEq h p p :=
  polynomial_residue_of_coeff_eq h p p (fun _=>rfl)

private theorem negative_product (p q : Poly K) (i : Nat) :
    (-p*q).coeff i= -(p*q).coeff i := by
  have same : PolynomialCoeffEq (-p) (Poly.zero-p) := by
    intro j;rw [Poly.coeff_sub,Poly.coeff_neg];change -p.coeff j=0-p.coeff j;grind
  rw [polynomial_mul_congr _ _ q q same (fun _=>rfl),polynomial_sub_mul,Poly.coeff_sub]
  change 0-(p*q).coeff i= -(p*q).coeff i
  grind

theorem polynomial_residue_symm (h p q : Poly K) (same : PolynomialResidueEq h p q) :
    PolynomialResidueEq h q p := by
  obtain ⟨s,identity⟩:=same
  refine ⟨-s,?_⟩
  intro i
  have entry:=identity i
  rw [Poly.coeff_sub] at entry
  rw [Poly.coeff_sub,negative_product]
  grind

theorem polynomial_residue_trans (h p q r : Poly K)
    (pq : PolynomialResidueEq h p q) (qr : PolynomialResidueEq h q r) :
    PolynomialResidueEq h p r := by
  obtain ⟨s,hs⟩:=pq
  obtain ⟨t,ht⟩:=qr
  refine ⟨s+t,?_⟩
  intro i
  have a:=hs i;have b:=ht i
  rw [Poly.coeff_sub] at a b
  rw [Poly.coeff_sub,polynomial_add_mul,Poly.coeff_add]
  grind

theorem polynomial_residue_add (h p p' q q' : Poly K)
    (hp : PolynomialResidueEq h p p') (hq : PolynomialResidueEq h q q') :
    PolynomialResidueEq h (p+q) (p'+q') := by
  obtain ⟨s,hs⟩:=hp
  obtain ⟨t,ht⟩:=hq
  refine ⟨s+t,?_⟩
  intro i
  have a:=hs i;have b:=ht i
  rw [Poly.coeff_sub] at a b
  rw [Poly.coeff_sub,Poly.coeff_add,Poly.coeff_add,polynomial_add_mul,Poly.coeff_add]
  grind

theorem polynomial_residue_neg (h p q : Poly K) (hp : PolynomialResidueEq h p q) :
    PolynomialResidueEq h (-p) (-q) := by
  obtain ⟨s,hs⟩:=hp
  refine ⟨-s,?_⟩
  intro i
  have a:=hs i
  rw [Poly.coeff_sub] at a
  rw [Poly.coeff_sub,Poly.coeff_neg,Poly.coeff_neg,negative_product]
  grind

private theorem multiply_right (h p q r : Poly K) (same : PolynomialResidueEq h p q) :
    PolynomialResidueEq h (p*r) (q*r) := by
  obtain ⟨s,hs⟩:=same
  refine ⟨s*r,?_⟩
  intro i
  have through:=polynomial_mul_congr (p-q) (s*h) r r hs (fun _=>rfl) i
  rw [polynomial_sub_mul,Poly.coeff_sub,polynomial_mul_assoc,
    polynomial_mul_congr s s (h*r) (r*h) (fun _=>rfl) (polynomial_mul_comm h r),
    ←polynomial_mul_assoc] at through
  rw [Poly.coeff_sub]
  exact through

theorem polynomial_residue_mul (h p p' q q' : Poly K)
    (hp : PolynomialResidueEq h p p') (hq : PolynomialResidueEq h q q') :
    PolynomialResidueEq h (p*q) (p'*q') := by
  apply polynomial_residue_trans h (p*q) (p'*q) (p'*q') (multiply_right h p p' q hp)
  apply polynomial_residue_trans h (p'*q) (q*p') (p'*q')
    (polynomial_residue_of_coeff_eq _ _ _ (polynomial_mul_comm p' q))
  exact polynomial_residue_trans h (q*p') (q'*p') (p'*q') (multiply_right h q q' p' hq)
    (polynomial_residue_of_coeff_eq _ _ _ (polynomial_mul_comm q' p'))

/-- Actual quotient by formal polynomial congruence; no evaluation sampling. -/
def polynomialResidueSetoid (h : Poly K) : Setoid (Poly K) where
  r := PolynomialResidueEq h
  iseqv := ⟨polynomial_residue_refl h,fun eq=>polynomial_residue_symm h _ _ eq,
    fun eq₁ eq₂=>polynomial_residue_trans h _ _ _ eq₁ eq₂⟩

abbrev PolynomialResidue (h : Poly K) := Quotient (polynomialResidueSetoid h)

def polynomialResidueClass (h p : Poly K) : PolynomialResidue h := Quotient.mk _ p

def polynomialResidueAdd (h : Poly K) : PolynomialResidue h → PolynomialResidue h → PolynomialResidue h :=
  Quotient.lift₂ (fun p q=>polynomialResidueClass h (p+q))
    (fun _ _ _ _ hp hq=>Quotient.sound (polynomial_residue_add h _ _ _ _ hp hq))

def polynomialResidueMul (h : Poly K) : PolynomialResidue h → PolynomialResidue h → PolynomialResidue h :=
  Quotient.lift₂ (fun p q=>polynomialResidueClass h (p*q))
    (fun _ _ _ _ hp hq=>Quotient.sound (polynomial_residue_mul h _ _ _ _ hp hq))

def polynomialResidueNeg (h : Poly K) : PolynomialResidue h → PolynomialResidue h :=
  Quotient.lift (fun p=>polynomialResidueClass h (-p))
    (fun _ _ hp=>Quotient.sound (polynomial_residue_neg h _ _ hp))

/-- Quotient equality is exactly formal divisibility of the difference. -/
theorem polynomial_residue_class_eq_iff (h p q : Poly K) :
    polynomialResidueClass h p=polynomialResidueClass h q ↔ PolynomialResidueEq h p q :=
  ⟨fun eq=>Quotient.exact eq,fun eq=>Quotient.sound (s:=polynomialResidueSetoid h) eq⟩

theorem polynomial_residue_zero_iff (h p : Poly K) :
    polynomialResidueClass h p=polynomialResidueClass h Poly.zero ↔ PolynomialDivides h p := by
  rw [polynomial_residue_class_eq_iff]
  constructor
  · intro ⟨s,eq⟩
    refine ⟨s,?_⟩
    intro i;have entry:=eq i;rw [Poly.coeff_sub] at entry
    change p.coeff i-0=(s*h).coeff i at entry
    grind
  · intro ⟨s,eq⟩
    refine ⟨s,?_⟩
    intro i;rw [Poly.coeff_sub]
    change p.coeff i-0=(s*h).coeff i
    rw [eq i];grind

/-- Nonzero quotient elements have inverse quotient elements, rather than
merely representative-level witnesses. -/
theorem polynomial_residue_quotient_inverse (h : Poly K)
    (irreducible : PolynomialIrreducible h) (x : PolynomialResidue h)
    (nonzero : x≠polynomialResidueClass h Poly.zero) :
    ∃ y : PolynomialResidue h, polynomialResidueMul h y x=polynomialResidueClass h (Poly.C 1) := by
  induction x using Quotient.inductionOn with
  | h p =>
    have pn : ¬PolynomialDivides h p := by
      intro divides;exact nonzero ((polynomial_residue_zero_iff h p).mpr divides)
    obtain ⟨d,_,_,hd,leading,_⟩:=polynomial_division_exists Poly.zero h irreducible.1
    obtain ⟨r,_,inverse⟩:=irreducible_residue_inverse h p d irreducible hd leading pn
    exact ⟨polynomialResidueClass h r,(polynomial_residue_class_eq_iff h _ _).mpr inverse⟩

theorem polynomial_residue_mul_assoc (h : Poly K) (x y z : PolynomialResidue h) :
    polynomialResidueMul h (polynomialResidueMul h x y) z=
      polynomialResidueMul h x (polynomialResidueMul h y z) := by
  induction x using Quotient.inductionOn with | h p =>
    induction y using Quotient.inductionOn with | h q =>
      induction z using Quotient.inductionOn with | h r =>
        exact (polynomial_residue_class_eq_iff h _ _).mpr
          (polynomial_residue_of_coeff_eq h _ _ (polynomial_mul_assoc p q r))

theorem polynomial_residue_mul_comm (h : Poly K) (x y : PolynomialResidue h) :
    polynomialResidueMul h x y=polynomialResidueMul h y x := by
  induction x using Quotient.inductionOn with | h p =>
    induction y using Quotient.inductionOn with | h q =>
      exact (polynomial_residue_class_eq_iff h _ _).mpr
        (polynomial_residue_of_coeff_eq h _ _ (polynomial_mul_comm p q))

theorem polynomial_residue_add_mul (h : Poly K) (x y z : PolynomialResidue h) :
    polynomialResidueMul h (polynomialResidueAdd h x y) z=
      polynomialResidueAdd h (polynomialResidueMul h x z) (polynomialResidueMul h y z) := by
  induction x using Quotient.inductionOn with | h p =>
    induction y using Quotient.inductionOn with | h q =>
      induction z using Quotient.inductionOn with | h r =>
        exact (polynomial_residue_class_eq_iff h _ _).mpr
          (polynomial_residue_of_coeff_eq h _ _ (polynomial_add_mul p q r))

/-- In particular the quotient has distinct zero and one for irreducible h. -/
theorem polynomial_residue_one_ne_zero (h : Poly K) (irreducible : PolynomialIrreducible h) :
    polynomialResidueClass h (Poly.C 1)≠polynomialResidueClass h Poly.zero := by
  intro same
  exact irreducible_residue_constant_nonzero h 1 irreducible
    (fun zero=>Field.zero_ne_one zero.symm) ((polynomial_residue_zero_iff h _).mp same)
end NearCompression
