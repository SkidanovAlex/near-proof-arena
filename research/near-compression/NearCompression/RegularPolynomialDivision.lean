import NearCompression.SeparableFactorSelection

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Every coefficient admits a safe partial value at the parameter point. -/
def RationalPolynomialRegularAt (p : Poly (PolynomialRational K)) (z : K) : Prop :=
  ∀ i,∃ v,PolynomialRationalValueAt (p.coeff i) z v

private theorem regular_zero (z : K) : ∃ v,PolynomialRationalValueAt (0 : PolynomialRational K) z v :=
  ⟨0,rational_coefficient_specializes 0 z⟩

private theorem regular_add (r s : PolynomialRational K) (z : K)
    (hr : ∃ v,PolynomialRationalValueAt r z v) (hs : ∃ v,PolynomialRationalValueAt s z v) :
    ∃ v,PolynomialRationalValueAt (r+s) z v := by
  obtain ⟨a,ha⟩:=hr;obtain ⟨b,hb⟩:=hs
  exact ⟨a+b,polynomial_rational_value_add r s z a b ha hb⟩

private theorem regular_mul (r s : PolynomialRational K) (z : K)
    (hr : ∃ v,PolynomialRationalValueAt r z v) (hs : ∃ v,PolynomialRationalValueAt s z v) :
    ∃ v,PolynomialRationalValueAt (r*s) z v := by
  obtain ⟨a,ha⟩:=hr;obtain ⟨b,hb⟩:=hs
  exact ⟨a*b,polynomial_rational_value_mul r s z a b ha hb⟩

private theorem regular_sub (r s : PolynomialRational K) (z : K)
    (hr : ∃ v,PolynomialRationalValueAt r z v) (hs : ∃ v,PolynomialRationalValueAt s z v) :
    ∃ v,PolynomialRationalValueAt (r-s) z v := by
  have negone : (polynomialRationalCoefficientMap (K:=K)).toFun (-1)= -1 := by
    have h:=(polynomialRationalCoefficientMap (K:=K)).add (-1) 1
    have zero : (-1:K)+1=0 := by grind
    rw [zero,polynomialRationalCoefficientMap.zero,polynomialRationalCoefficientMap.one] at h
    grind
  have negative : ∃ v,PolynomialRationalValueAt (-1 : PolynomialRational K) z v := by
    rw [←negone];exact ⟨-1,rational_coefficient_specializes (-1) z⟩
  have result:=regular_add r ((-1)*s) z hr (regular_mul (-1) s z negative hs)
  have same : r+(-1)*s=r-s := by grind
  rwa [same] at result

theorem rational_polynomial_regular_add (p q : Poly (PolynomialRational K)) (z : K)
    (hp : RationalPolynomialRegularAt p z) (hq : RationalPolynomialRegularAt q z) :
    RationalPolynomialRegularAt (p+q) z := by
  intro i;rw [Poly.coeff_add];exact regular_add _ _ z (hp i) (hq i)

theorem rational_polynomial_regular_sub (p q : Poly (PolynomialRational K)) (z : K)
    (hp : RationalPolynomialRegularAt p z) (hq : RationalPolynomialRegularAt q z) :
    RationalPolynomialRegularAt (p-q) z := by
  intro i;rw [Poly.coeff_sub];exact regular_sub _ _ z (hp i) (hq i)

private theorem regular_dot (xs : List Nat) (a b : Nat→PolynomialRational K) (z : K)
    (ha : ∀ i,∃ v,PolynomialRationalValueAt (a i) z v)
    (hb : ∀ i,∃ v,PolynomialRationalValueAt (b i) z v) :
    ∃ v,PolynomialRationalValueAt (kernelDot xs a b) z v := by
  induction xs with
  | nil => exact regular_zero z
  | cons i xs ih => exact regular_add _ _ z (regular_mul _ _ z (ha i) (hb i)) ih

theorem rational_polynomial_regular_mul (p q : Poly (PolynomialRational K)) (z : K)
    (hp : RationalPolynomialRegularAt p z) (hq : RationalPolynomialRegularAt q z) :
    RationalPolynomialRegularAt (p*q) z := by
  intro i
  rw [polynomial_bounded_product_coefficient p q p.coeffs.length i (Poly.degLt_length p)]
  apply regular_dot _ _ _ z hp
  intro j
  split
  · exact hq _
  · exact regular_zero z

private theorem regular_constant (c : PolynomialRational K) (z : K)
    (hc : ∃ v,PolynomialRationalValueAt c z v) : RationalPolynomialRegularAt (Poly.C c) z := by
  intro i;cases i with
  | zero => exact hc
  | succ i => exact regular_zero z

private theorem regular_monomial (n : Nat) (z : K) :
    RationalPolynomialRegularAt (jetMonomial n) z := by
  intro i;rw [jet_monomial_coefficient]
  split
  · exact ⟨1,rational_coefficient_specializes 1 z⟩
  · exact regular_zero z

private theorem constant_product (c : PolynomialRational K) (q : Poly (PolynomialRational K)) (i : Nat) :
    (Poly.C c*q).coeff i=c*q.coeff i := by
  change (Poly.smul c q+Poly.mk [0]).coeff i=_
  rw [Poly.coeff_add,Poly.coeff_smul]
  have zero : (Poly.mk [0] : Poly (PolynomialRational K)).coeff i=0 := by cases i <;> rfl
  rw [zero];grind

/-- Long division stays regular at a specialization point provided the
specialized leading coefficient is nonzero. This rules out hidden quotient
poles when comparing representatives of an algebraic extension. -/
theorem rational_polynomial_regular_division
    (q : Poly (PolynomialRational K)) (d n : Nat) (z leadingValue : K)
    (qd : q.DegLt (d+1)) (ql : q.coeff d≠0)
    (qr : RationalPolynomialRegularAt q z)
    (leadingSpecializes : PolynomialRationalValueAt (q.coeff d) z leadingValue)
    (leadingSafe : leadingValue≠0)
    (p : Poly (PolynomialRational K)) (pd : p.DegLt (n+d))
    (pr : RationalPolynomialRegularAt p z) :
    ∃ quotient remainder : Poly (PolynomialRational K),
      quotient.DegLt n ∧ remainder.DegLt d ∧ PolynomialCoeffEq p (quotient*q+remainder) ∧
      RationalPolynomialRegularAt quotient z ∧ RationalPolynomialRegularAt remainder z := by
  induction n generalizing p with
  | zero =>
    refine ⟨Poly.zero,p,?_,?_,?_,?_,pr⟩
    · intro i hi;rfl
    · simpa only [Nat.zero_add] using pd
    · intro i;rw [Poly.coeff_add];change p.coeff i=0+p.coeff i;grind
    · intro i;exact regular_zero z
  | succ n ih =>
    let c:=p.coeff (n+d)*(q.coeff d)⁻¹
    let correction:=Poly.C c*jetMonomial n
    have cr : ∃ v,PolynomialRationalValueAt c z v := regular_mul _ _ z (pr (n+d))
      ⟨_,polynomial_rational_value_inv _ z _ leadingSpecializes leadingSafe⟩
    have correctionRegular : RationalPolynomialRegularAt correction z :=
      rational_polynomial_regular_mul _ _ z (regular_constant c z cr) (regular_monomial n z)
    have monomialDegree : (jetMonomial n : Poly (PolynomialRational K)).DegLt (n+1) := by
      intro i hi;rw [jet_monomial_coefficient,ite_eq_right (by omega)]
    have correctionDegree : correction.DegLt (n+1) := by
      simpa only [List.length_nil,Nat.zero_add] using
        (Poly.degLt_mul (Poly.degLt_length (Poly.C c)) monomialDegree)
    have productDegree : (correction*q).DegLt (n+d+1) := Poly.degLt_mul correctionDegree qd
    have cancel : (correction*q).coeff (n+d)=p.coeff (n+d) := by
      dsimp only [correction]
      rw [polynomial_mul_assoc,constant_product,polynomial_monomial_mul_coefficient,ite_eq_right (by omega)]
      have index : n+d-n=d := by omega
      rw [index]
      have inverse:=Field.mul_inv_cancel ql
      dsimp only [c];grind
    have smaller : (p-correction*q).DegLt (n+d) := by
      intro i hi;rw [Poly.coeff_sub]
      by_cases top : i=n+d
      · rw [top,cancel];grind
      · rw [pd i (by omega),productDegree i (by omega)];grind
    have reducedRegular:=rational_polynomial_regular_sub p (correction*q) z pr
      (rational_polynomial_regular_mul correction q z correctionRegular qr)
    obtain ⟨a,r,ad,rd,equation,ar,rr⟩:=ih (p-correction*q) smaller reducedRegular
    refine ⟨a+correction,r,Poly.degLt_add (Poly.DegLt.mono ad (by omega)) correctionDegree,rd,?_,
      rational_polynomial_regular_add a correction z ar correctionRegular,rr⟩
    intro i
    have h:=equation i
    rw [Poly.coeff_sub,Poly.coeff_add] at h
    rw [Poly.coeff_add,polynomial_add_mul,Poly.coeff_add]
    grind
/-- Exact divisibility has a regular quotient when the input and modulus are
regular and the specialized leading coefficient does not vanish. The original
divisibility witness may have been presented using poles. -/
theorem rational_polynomial_regular_exact_quotient
    (p q : Poly (PolynomialRational K)) (d : Nat) (z leadingValue : K)
    (qd : q.DegLt (d+1)) (ql : q.coeff d≠0)
    (qr : RationalPolynomialRegularAt q z) (pr : RationalPolynomialRegularAt p z)
    (leadingSpecializes : PolynomialRationalValueAt (q.coeff d) z leadingValue)
    (leadingSafe : leadingValue≠0) (divides : PolynomialDivides q p) :
    ∃ t : Poly (PolynomialRational K), RationalPolynomialRegularAt t z ∧ PolynomialCoeffEq p (t*q) := by
  obtain ⟨t,r,_,rd,division,tr,_⟩:=rational_polynomial_regular_division q d p.coeffs.length z leadingValue
    qd ql qr leadingSpecializes leadingSafe p (Poly.DegLt.mono (Poly.degLt_length p) (by omega)) pr
  obtain ⟨s,divisibility⟩:=divides
  have residue : PolynomialResidueEq q r Poly.zero := by
    refine ⟨s-t,?_⟩
    have eq:=(formal_polynomial_eq_iff _ _).mpr division
    have div:=(formal_polynomial_eq_iff _ _).mpr divisibility
    change formalPolynomial p=formalPolynomial t*formalPolynomial q+formalPolynomial r at eq
    change formalPolynomial p=formalPolynomial s*formalPolynomial q at div
    apply (formal_polynomial_eq_iff _ _).mp
    change formalPolynomial r-formalPolynomial Poly.zero=(formalPolynomial s-formalPolynomial t)*formalPolynomial q
    have zero : formalPolynomial (Poly.zero : Poly (PolynomialRational K))=0 :=
      (formal_polynomial_zero_iff _).mpr (by intro i;rfl)
    rw [zero];grind
  have rz:=polynomial_reduced_residue_unique q r Poly.zero d ql rd (by intro i hi;rfl) residue
  refine ⟨t,tr,?_⟩
  intro i
  rw [division i,Poly.coeff_add,rz i]
  change (t*q).coeff i+0=(t*q).coeff i
  grind
end NearCompression
