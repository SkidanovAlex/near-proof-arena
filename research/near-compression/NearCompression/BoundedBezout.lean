import NearCompression.RationalCoefficientGuards

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem constant_product (c : K) (q : Poly K) (i : Nat) :
    (Poly.C c*q).coeff i=c*q.coeff i := by
  change (Poly.smul c q+Poly.mk [0]).coeff i=_
  rw [Poly.coeff_add,Poly.coeff_smul]
  have zero : (Poly.mk [0] : Poly K).coeff i=0 := by cases i <;> rfl
  rw [zero];grind

/-- Reduce any unit Bezout certificate to multipliers with fewer than n and m
coefficients respectively, where deg(q)=n and deg(p)≤m. -/
theorem polynomial_bezout_degree_reduction (p q A B : Poly K) (m n : Nat)
    (mp : 0<m) (pd : p.DegLt (m+1)) (qd : q.DegLt (n+1)) (ql : q.coeff n≠0)
    (certificate : PolynomialCoeffEq (A*p+B*q) (Poly.C 1)) :
    ∃ U V : Poly K, U.DegLt n ∧ V.DegLt m ∧ PolynomialCoeffEq (U*p+V*q) (Poly.C 1) := by
  by_cases nz : n=0
  · subst n
    refine ⟨Poly.zero,Poly.C ((q.coeff 0)⁻¹),(by intro i hi;rfl),
      Poly.DegLt.mono (Poly.degLt_length _) mp,?_⟩
    intro i
    rw [Poly.coeff_add,constant_product]
    have inverse:=Field.mul_inv_cancel ql
    cases i with
    | zero => change 0+(q.coeff 0)⁻¹*q.coeff 0=1;grind
    | succ i =>
      rw [qd (i+1) (by omega)]
      change (0:K)+(q.coeff 0)⁻¹*0=0;grind
  · obtain ⟨t,r,_,rd,division⟩:=polynomial_division_bounded q n A.coeffs.length qd ql A
      (Poly.DegLt.mono (Poly.degLt_length A) (by omega))
    let s:=B+t*p
    have newcert : PolynomialCoeffEq (r*p+s*q) (Poly.C 1) := by
      intro i
      have through:=polynomial_mul_congr A (t*q+r) p p division (fun _=>rfl) i
      rw [polynomial_add_mul,Poly.coeff_add,polynomial_mul_assoc,
        polynomial_mul_congr t t (q*p) (p*q) (fun _=>rfl) (polynomial_mul_comm q p),
        ←polynomial_mul_assoc] at through
      have entry:=certificate i
      rw [Poly.coeff_add,through] at entry
      dsimp only [s]
      rw [Poly.coeff_add,polynomial_add_mul,Poly.coeff_add]
      grind
    have productDegree : (r*p).DegLt (n+m) := by
      have nr : r.DegLt ((n-1)+1) := by simpa only [Nat.sub_add_cancel (show 1≤n by omega)] using rd
      have result:=Poly.degLt_mul nr pd
      have index : n-1+m+1=n+m := by omega
      rwa [index] at result
    have sqDegree : (s*q).DegLt (n+m) := by
      intro i hi
      have entry:=newcert i
      rw [Poly.coeff_add,productDegree i hi] at entry
      have one : (Poly.C (1:K)).coeff i=0 := by cases i with | zero => omega | succ i => rfl
      rw [one] at entry
      grind
    have sd : s.DegLt m := by
      by_cases sz : s.IsZero
      · exact fun i _=>sz i
      · obtain ⟨j,_,_,jd,jl,_⟩:=polynomial_division_exists Poly.zero s sz
        have bound : j<m := by
          apply Classical.byContradiction
          intro bad
          have entry:=sqDegree (j+n) (by omega)
          rw [polynomial_leading_product s q j n jd qd] at entry
          rcases Field.of_mul_eq_zero entry with zero|zero
          · exact jl zero
          · exact ql zero
        exact Poly.DegLt.mono jd bound
    exact ⟨r,s,rd,sd,newcert⟩

/-- For degree-d irreducibles below the characteristic, a derivative certificate
needs at most d-1 plus d coefficient unknowns, including the linear case. -/
theorem irreducible_bounded_derivative_bezout (characteristic : Nat) [IsCharP K characteristic]
    (p : Poly K) (d : Nat) (irreducible : PolynomialIrreducible p)
    (degree : p.DegLt (d+1)) (leading : p.coeff d≠0)
    (positive : 0<d) (small : d<characteristic) :
    ∃ A B : Poly K, A.DegLt (d-1) ∧ B.DegLt d ∧
      PolynomialCoeffEq (A*p+B*polynomialDerivative p) (Poly.C 1) := by
  obtain ⟨A,B,certificate⟩:=irreducible_derivative_bezout characteristic p d irreducible degree leading positive small
  have dd : (polynomialDerivative p).DegLt (d-1+1) := by
    have same : d-1+1=d := by omega
    rw [same]
    exact polynomial_derivative_degree p d degree
  have dl : (polynomialDerivative p).coeff (d-1)≠0 := by
    rw [polynomial_derivative_coefficient]
    have same : d-1+1=d := by omega
    rw [same]
    intro zero
    rcases Field.of_mul_eq_zero zero with scalar|coefficient
    · have modular:=(IsCharP.natCast_eq_zero_iff characteristic d).mp scalar
      rw [Nat.mod_eq_of_lt small] at modular
      omega
    · exact leading coefficient
  exact polynomial_bezout_degree_reduction p (polynomialDerivative p) A B d (d-1)
    positive degree dd dl certificate

private theorem bounded_product (a b : Poly K) (m n : Nat)
    (ad : a.DegLt m) (bd : b.DegLt (n+1)) : (a*b).DegLt (m+n) := by
  cases m with
  | zero =>
    have zero : a.IsZero := fun i=>ad i (Nat.zero_le i)
    have product:=(polynomial_product_zero_iff a b).mpr (Or.inl zero)
    exact fun i _=>product i
  | succ m =>
    have bound:=Poly.degLt_mul ad bd
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bound

/-- With bounded multipliers, checking m+n coefficients proves the entire
formal identity, including arbitrary trailing-zero list representations. -/
theorem polynomial_bounded_bezout_finite_check (p q A B : Poly K) (m n : Nat)
    (positive : 0<m+n) (pd : p.DegLt (m+1)) (qd : q.DegLt (n+1))
    (ad : A.DegLt n) (bd : B.DegLt m)
    (checked : ∀ i, i<m+n → (A*p+B*q).coeff i=(Poly.C (1:K)).coeff i) :
    PolynomialCoeffEq (A*p+B*q) (Poly.C 1) := by
  have left : (A*p).DegLt (m+n) := by
    simpa only [Nat.add_comm] using bounded_product A p n m ad pd
  have right:=bounded_product B q m n bd qd
  have degree:=Poly.degLt_add left right
  intro i
  by_cases hi : i<m+n
  · exact checked i hi
  · rw [degree i (by omega)]
    cases i with | zero => omega | succ i => rfl

/-- The derivative Bezout problem has exactly 2d-1 possibly nonzero
coefficient equations once its multiplier degree bounds are enforced. -/
theorem polynomial_derivative_bezout_finite_check (p A B : Poly K) (d : Nat)
    (positive : 0<d) (pd : p.DegLt (d+1)) (ad : A.DegLt (d-1)) (bd : B.DegLt d)
    (checked : ∀ i, i<2*d-1 → (A*p+B*polynomialDerivative p).coeff i=(Poly.C (1:K)).coeff i) :
    PolynomialCoeffEq (A*p+B*polynomialDerivative p) (Poly.C 1) := by
  have same : d-1+1=d := by omega
  have derivative : (polynomialDerivative p).DegLt (d-1+1) := by
    rw [same];exact polynomial_derivative_degree p d pd
  apply polynomial_bounded_bezout_finite_check p (polynomialDerivative p) A B d (d-1)
    (by omega) pd derivative ad bd
  intro i hi
  exact checked i (by omega)
end NearCompression
