import NearCompression.SyntheticJetLinear

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem cons_product (c : K) (cs : List K) (q : Poly K) (i : Nat) :
    ((Poly.mk (c::cs))*q).coeff i=c*q.coeff i+
      (match i with | 0=>0 | j+1=>((Poly.mk cs)*q).coeff j) := by
  change (Poly.smul c q+Poly.mk (0::Poly.mulL cs q.coeffs)).coeff i=_
  rw [Poly.coeff_add,Poly.coeff_smul]
  cases i <;> rfl

private theorem zero_product (q : Poly K) (i : Nat) : (Poly.zero*q).coeff i=0 := rfl
private theorem product_zero (p : Poly K) (i : Nat) : (p*Poly.zero).coeff i=0 := by
  have h:=polynomial_order_mul 0 (i+1) p Poly.zero (by intro j hj;omega) (by intro j hj;rfl)
  exact h i (by omega)

/-- Multiplication respects formal coefficient equality, including padding. -/
theorem polynomial_mul_congr (p p' q q' : Poly K)
    (hp : PolynomialCoeffEq p p') (hq : PolynomialCoeffEq q q') :
    PolynomialCoeffEq (p*q) (p'*q') := by
  intro i
  induction i generalizing p p' with
  | zero =>
    cases p with | mk ps => cases ps with
      | nil =>
        cases p' with | mk ps' => cases ps' with
          | nil => rfl
          | cons c cs =>
            have head:=hp 0
            rw [cons_product]
            change 0=c*q'.coeff 0+0
            change 0=c at head
            rw [←head];grind
      | cons c cs =>
        cases p' with | mk ps' => cases ps' with
          | nil =>
            have head:=hp 0
            rw [cons_product]
            change c*q.coeff 0+0=0
            change c=0 at head
            rw [head];grind
          | cons d ds =>
            rw [cons_product,cons_product]
            have head:=hp 0
            change c=d at head
            rw [head,hq]
  | succ i ih =>
    cases p with | mk ps => cases p' with | mk ps' =>
      cases ps with
      | nil =>
        cases ps' with
        | nil => rfl
        | cons d ds =>
          have head:=hp 0
          change 0=d at head
          have tail : PolynomialCoeffEq Poly.zero (Poly.mk ds) := fun j=>hp (j+1)
          have h:=ih Poly.zero (Poly.mk ds) tail
          rw [cons_product]
          change 0=d*q'.coeff (i+1)+((Poly.mk ds)*q').coeff i
          rw [←head,←h];simp only [zero_product];grind
      | cons c cs =>
        cases ps' with
        | nil =>
          have head:=hp 0
          change c=0 at head
          have tail : PolynomialCoeffEq (Poly.mk cs) Poly.zero := fun j=>hp (j+1)
          have h:=ih (Poly.mk cs) Poly.zero tail
          rw [cons_product]
          change c*q.coeff (i+1)+((Poly.mk cs)*q).coeff i=0
          rw [head,h];simp only [zero_product];grind
        | cons d ds =>
          have head:=hp 0
          change c=d at head
          have tail : PolynomialCoeffEq (Poly.mk cs) (Poly.mk ds) := fun j=>hp (j+1)
          rw [cons_product,cons_product]
          change c*q.coeff (i+1)+((Poly.mk cs)*q).coeff i=d*q'.coeff (i+1)+((Poly.mk ds)*q').coeff i
          rw [head,hq,ih (Poly.mk cs) (Poly.mk ds) tail]

/-- Coefficientwise left distributivity. -/
theorem polynomial_add_mul (p q r : Poly K) : PolynomialCoeffEq ((p+q)*r) (p*r+q*r) := by
  cases p with | mk ps =>
    induction ps generalizing q with
    | nil => intro i;rw [Poly.coeff_add];change (q*r).coeff i=0+(q*r).coeff i;grind
    | cons c cs ih =>
      cases q with | mk qs => cases qs with
        | nil => intro i;rw [Poly.coeff_add];change ((Poly.mk (c::cs))*r).coeff i=((Poly.mk (c::cs))*r).coeff i+0;grind
        | cons d ds =>
          intro i
          change ((Poly.mk ((c+d)::Poly.addL cs ds))*r).coeff i=_
          rw [Poly.coeff_add,cons_product,cons_product,cons_product]
          cases i with
          | zero => grind
          | succ i =>
            have h:=ih (Poly.mk ds) i
            rw [Poly.coeff_add] at h
            change ((Poly.mk (Poly.addL cs ds))*r).coeff i=((Poly.mk cs)*r).coeff i+((Poly.mk ds)*r).coeff i at h
            simp only []
            rw [h];grind

private theorem scale_mul (c : K) (p q : Poly K) (i : Nat) :
    ((Poly.smul c p)*q).coeff i=c*(p*q).coeff i := by
  cases p with | mk ps =>
    induction ps generalizing i with
    | nil => change 0=c*0;grind
    | cons d ds ih =>
      change ((Poly.mk ((c*d)::Poly.scaleL c ds))*q).coeff i=c*((Poly.mk (d::ds))*q).coeff i
      rw [cons_product,cons_product]
      cases i with
      | zero => grind
      | succ i =>
        change c*d*q.coeff (i+1)+((Poly.smul c (Poly.mk ds))*q).coeff i=
          c*(d*q.coeff (i+1)+((Poly.mk ds)*q).coeff i)
        rw [ih];grind

/-- Formal associativity; no evaluation uniqueness assumption. -/
theorem polynomial_mul_assoc (p q r : Poly K) : PolynomialCoeffEq ((p*q)*r) (p*(q*r)) := by
  cases p with | mk ps =>
    induction ps with
    | nil => intro i;rfl
    | cons c cs ih =>
      intro i
      change ((Poly.smul c q+Poly.mk (0::Poly.mulL cs q.coeffs))*r).coeff i=_
      rw [polynomial_add_mul,Poly.coeff_add,scale_mul,cons_product,cons_product]
      cases i with
      | zero => grind
      | succ i =>
        change c*(q*r).coeff (i+1)+(0*r.coeff (i+1)+((Poly.mk cs*q)*r).coeff i)=
          c*(q*r).coeff (i+1)+(Poly.mk cs*(q*r)).coeff i
        rw [ih];grind
private theorem product_cons_right (p : Poly K) (c : K) (cs : List K) (i : Nat) :
    (p*(Poly.mk (c::cs))).coeff i=c*p.coeff i+
      (match i with | 0=>0 | j+1=>(p*(Poly.mk cs)).coeff j) := by
  cases p with | mk ps =>
    induction ps generalizing i with
    | nil => cases i <;> change 0=c*0+0 <;> grind
    | cons d ds ih =>
      rw [cons_product]
      cases i with
      | zero => change d*c+0=c*d+0;grind
      | succ i =>
        change d*(Poly.mk cs).coeff i+((Poly.mk ds)*(Poly.mk (c::cs))).coeff i=
          c*(Poly.mk ds).coeff i+((Poly.mk (d::ds))*(Poly.mk cs)).coeff i
        rw [ih,cons_product]
        cases i <;> simp only [] <;> grind

/-- Formal commutativity over coefficient lists with arbitrary zero padding. -/
theorem polynomial_mul_comm (p q : Poly K) : PolynomialCoeffEq (p*q) (q*p) := by
  cases p with | mk ps =>
    induction ps with
    | nil => intro i;change 0=(q*Poly.zero).coeff i;rw [product_zero]
    | cons c cs ih =>
      intro i
      rw [cons_product,product_cons_right]
      cases i with
      | zero => rfl
      | succ i => change c*q.coeff (i+1)+((Poly.mk cs)*q).coeff i=c*q.coeff (i+1)+(q*(Poly.mk cs)).coeff i;rw [ih]

theorem polynomial_mul_add (p q r : Poly K) : PolynomialCoeffEq (p*(q+r)) (p*q+p*r) := by
  intro i
  rw [polynomial_mul_comm p (q+r),polynomial_add_mul,Poly.coeff_add,Poly.coeff_add,
    polynomial_mul_comm q p,polynomial_mul_comm r p]

theorem polynomial_sub_mul (p q r : Poly K) : PolynomialCoeffEq ((p-q)*r) (p*r-q*r) := by
  intro i
  change ((p+Poly.smul (-1) q)*r).coeff i=_
  rw [polynomial_add_mul,Poly.coeff_add,scale_mul,Poly.coeff_sub]
  grind
end NearCompression
