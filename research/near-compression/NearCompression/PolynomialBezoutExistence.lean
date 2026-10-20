import NearCompression.PolynomialDivision

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Formal divisibility modulo coefficient equality, so zero padding is irrelevant. -/
def PolynomialDivides (g p : Poly K) : Prop :=
  ∃ a : Poly K,PolynomialCoeffEq p (a*g)

private theorem constant_product (c : K) (q : Poly K) (i : Nat) :
    (Poly.C c*q).coeff i=c*q.coeff i := by
  change (Poly.smul c q+Poly.mk (0::[])).coeff i=_
  rw [Poly.coeff_add,Poly.coeff_smul]
  have zero : (Poly.mk [0] : Poly K).coeff i=0 := by cases i <;> simp [Poly.coeff,List.getD]
  rw [zero];grind

private theorem mul_sub (p q r : Poly K) : PolynomialCoeffEq (p*(q-r)) (p*q-p*r) := by
  intro i
  rw [polynomial_mul_comm p (q-r),polynomial_sub_mul,Poly.coeff_sub,Poly.coeff_sub,
    polynomial_mul_comm q p,polynomial_mul_comm r p]

/-- Degree-decreasing Euclidean construction: a nonzero common divisor and
its Bezout coefficients exist, with degree below the first input's bound. -/
theorem polynomial_bezout_gcd_exists (bound : Nat) (p q : Poly K)
    (nonzero : ¬p.IsZero) (degree : p.DegLt bound) :
    ∃ g A B : Poly K,¬g.IsZero ∧ g.DegLt bound ∧
      PolynomialCoeffEq g (A*p+B*q) ∧ PolynomialDivides g p ∧ PolynomialDivides g q := by
  induction bound using Nat.strongRecOn generalizing p q with
  | ind bound ih =>
    obtain ⟨d,t,r,pd,leading,rd,division⟩:=polynomial_division_exists q p nonzero
    have smaller : d<bound := by
      apply Classical.byContradiction
      intro h
      exact leading (degree d (by omega))
    by_cases zero : r.IsZero
    · refine ⟨p,Poly.C 1,Poly.zero,nonzero,degree,?_,?_,?_⟩
      · intro i
        rw [Poly.coeff_add,constant_product]
        change p.coeff i=1*p.coeff i+0
        grind
      · exact ⟨Poly.C 1,by intro i;rw [constant_product];grind⟩
      · refine ⟨t,?_⟩
        intro i
        have h:=division i
        rw [Poly.coeff_add,zero i] at h
        grind
    · obtain ⟨g,U,V,gnz,gd,identity,gr,gp⟩:=ih d smaller r p zero rd
      obtain ⟨b,br⟩:=gr
      obtain ⟨c,cp⟩:=gp
      have remainder : PolynomialCoeffEq r (q-t*p) := by
        intro i
        have h:=division i
        rw [Poly.coeff_add] at h
        rw [Poly.coeff_sub]
        grind
      refine ⟨g,V-U*t,U,gnz,Poly.DegLt.mono gd (by omega),?_,⟨c,cp⟩,?_⟩
      · intro i
        have through:=polynomial_mul_congr U U r (q-t*p) (fun _=>rfl) remainder i
        rw [mul_sub,Poly.coeff_sub] at through
        have h:=identity i
        rw [Poly.coeff_add,through] at h
        rw [Poly.coeff_add,polynomial_sub_mul,Poly.coeff_sub,polynomial_mul_assoc]
        grind
      · refine ⟨t*c+b,?_⟩
        intro i
        have through:=polynomial_mul_congr t t p (c*g) (fun _=>rfl) cp i
        have h:=division i
        rw [Poly.coeff_add,through,br i] at h
        rw [polynomial_add_mul,Poly.coeff_add,polynomial_mul_assoc]
        exact h

/-- Any common divisor divides any formal Bezout combination; thus the
constructed nonzero common divisor has the greatest-divisor property. -/
theorem polynomial_common_divisor_divides_bezout (d p q g A B : Poly K)
    (dp : PolynomialDivides d p) (dq : PolynomialDivides d q)
    (certificate : PolynomialCoeffEq g (A*p+B*q)) : PolynomialDivides d g := by
  obtain ⟨a,pa⟩:=dp
  obtain ⟨b,qb⟩:=dq
  refine ⟨A*a+B*b,?_⟩
  intro i
  have left:=polynomial_mul_congr A A p (a*d) (fun _=>rfl) pa i
  have right:=polynomial_mul_congr B B q (b*d) (fun _=>rfl) qb i
  have h:=certificate i
  rw [Poly.coeff_add,left,right] at h
  rw [polynomial_add_mul,Poly.coeff_add,polynomial_mul_assoc,polynomial_mul_assoc]
  exact h

/-- Coprimality stated intrinsically: every common divisor is a nonzero
constant polynomial. The Euclidean construction supplies a unit certificate. -/
theorem polynomial_coprime_bezout_exists (p q : Poly K) (nonzero : ¬p.IsZero)
    (coprime : ∀ g : Poly K,PolynomialDivides g p→PolynomialDivides g q→
      ∃ c : K,c≠0 ∧ PolynomialCoeffEq g (Poly.C c)) :
    ∃ A B : Poly K,PolynomialCoeffEq (A*p+B*q) (Poly.C 1) := by
  obtain ⟨g,A,B,gnz,gd,identity,gp,gq⟩:=polynomial_bezout_gcd_exists p.coeffs.length p q nonzero (Poly.degLt_length p)
  obtain ⟨c,cnz,constant⟩:=coprime g gp gq
  refine ⟨Poly.C (c⁻¹)*A,Poly.C (c⁻¹)*B,?_⟩
  intro i
  rw [Poly.coeff_add,polynomial_mul_assoc,constant_product,polynomial_mul_assoc,constant_product]
  have h:=identity i
  rw [Poly.coeff_add] at h
  have value:=constant i
  have inverse:=Field.mul_inv_cancel cnz
  cases i with
  | zero =>
    change g.coeff 0=c at value
    change c⁻¹*(A*p).coeff 0+c⁻¹*(B*q).coeff 0=1
    grind
  | succ i =>
    have cg : (Poly.C c).coeff (i+1)=0 := by simp [Poly.C,Poly.coeff,List.getD]
    have one : (Poly.C (1:K)).coeff (i+1)=0 := by simp [Poly.C,Poly.coeff,List.getD]
    rw [cg] at value
    rw [one]
    grind
end NearCompression
