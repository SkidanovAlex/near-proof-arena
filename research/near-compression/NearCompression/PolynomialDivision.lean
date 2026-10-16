import NearCompression.BezoutSmoothness

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem cons_product (c : K) (cs : List K) (q : Poly K) (i : Nat) :
    ((Poly.mk (c::cs))*q).coeff i=c*q.coeff i+
      (match i with | 0=>0 | j+1=>((Poly.mk cs)*q).coeff j) := by
  change (Poly.smul c q+Poly.mk (0::Poly.mulL cs q.coeffs)).coeff i=_
  rw [Poly.coeff_add,Poly.coeff_smul]
  cases i <;> rfl

private theorem constant_product (c : K) (q : Poly K) (i : Nat) :
    (Poly.C c*q).coeff i=c*q.coeff i := by
  change ((Poly.mk (c::[]))*q).coeff i=_
  rw [cons_product]
  cases i <;> change c*q.coeff _+0=c*q.coeff _ <;> grind

private theorem monomial_shift (n : Nat) :
    PolynomialCoeffEq (jetMonomial (n+1) : Poly K) (Poly.mk (0::(jetMonomial n : Poly K).coeffs)) := by
  intro i
  rw [jet_monomial_coefficient]
  cases i with
  | zero => simp only [Nat.zero_ne_add_one,ite_false];rfl
  | succ i =>
    change (if i+1=n+1 then (1:K) else 0)=(jetMonomial n : Poly K).coeff i
    rw [jet_monomial_coefficient]
    simp only [Nat.add_right_cancel_iff]

/-- Monomial multiplication is the exact coefficient shift, not merely an
identity of evaluations. -/
theorem polynomial_monomial_mul_coefficient (q : Poly K) (n i : Nat) :
    ((jetMonomial n)*q).coeff i=if i<n then 0 else q.coeff (i-n) := by
  induction n generalizing i with
  | zero =>
    change (Poly.C 1*q).coeff i=_
    rw [constant_product]
    simp only [Nat.not_lt_zero,ite_false,Nat.sub_zero]
    grind
  | succ n ih =>
    rw [polynomial_mul_congr _ _ q q (monomial_shift n) (fun _=>rfl) i,cons_product]
    cases i with
    | zero => simp only [Nat.zero_lt_succ,ite_true];grind
    | succ i =>
      change 0*q.coeff (i+1)+((jetMonomial n)*q).coeff i=if i+1<n+1 then 0 else q.coeff (i+1-(n+1))
      rw [ih]
      simp only [Nat.add_lt_add_iff_right,Nat.add_sub_add_right]
      grind

private theorem monomial_degree (n : Nat) : (jetMonomial n : Poly K).DegLt (n+1) := by
  intro i hi
  rw [jet_monomial_coefficient,ite_eq_right (by omega)]

/-- General long-division existence with explicit degree bounds. Divisor
leading coefficient must be nonzero; constant divisors and zero input work. -/
theorem polynomial_division_bounded (q : Poly K) (d n : Nat)
    (divisorDegree : q.DegLt (d+1)) (leading : q.coeff d≠0)
    (p : Poly K) (degree : p.DegLt (n+d)) :
    ∃ quotient remainder : Poly K,
      quotient.DegLt n ∧ remainder.DegLt d ∧ PolynomialCoeffEq p (quotient*q+remainder) := by
  induction n generalizing p with
  | zero =>
    refine ⟨Poly.zero,p,?_,?_,?_⟩
    · intro i hi;rfl
    · simpa only [Nat.zero_add] using degree
    · intro i;rw [Poly.coeff_add];change p.coeff i=0+p.coeff i;grind
  | succ n ih =>
    let c:=p.coeff (n+d)*(q.coeff d)⁻¹
    let correction:=Poly.C c*jetMonomial n
    have correctionDegree : correction.DegLt (n+1) := by
      simpa only [List.length_nil,Nat.zero_add] using
        (Poly.degLt_mul (Poly.degLt_length (Poly.C c)) (monomial_degree n))
    have productDegree : (correction*q).DegLt (n+d+1) := Poly.degLt_mul correctionDegree divisorDegree
    have cancel : (correction*q).coeff (n+d)=p.coeff (n+d) := by
      dsimp only [correction]
      rw [polynomial_mul_assoc,constant_product,polynomial_monomial_mul_coefficient,
        ite_eq_right (by omega)]
      have index : n+d-n=d := by omega
      rw [index]
      have inverse:=Field.mul_inv_cancel leading
      dsimp only [c]
      grind
    have smaller : (p-correction*q).DegLt (n+d) := by
      intro i hi
      rw [Poly.coeff_sub]
      by_cases top : i=n+d
      · rw [top,cancel];grind
      · rw [degree i (by omega),productDegree i (by omega)];grind
    obtain ⟨a,r,ad,rd,equation⟩:=ih (p-correction*q) smaller
    refine ⟨a+correction,r,Poly.degLt_add (Poly.DegLt.mono ad (by omega)) correctionDegree,rd,?_⟩
    intro i
    have h:=equation i
    rw [Poly.coeff_sub,Poly.coeff_add] at h
    rw [Poly.coeff_add,polynomial_add_mul,Poly.coeff_add]
    grind

private theorem leading_exists (q : Poly K) (nonzero : ¬q.IsZero) :
    ∃ d,q.DegLt (d+1) ∧ q.coeff d≠0 := by
  cases q with | mk cs =>
    induction cs with
    | nil => exact False.elim (nonzero (by intro i;simp [Poly.coeff]))
    | cons c cs ih =>
      by_cases tail : (Poly.mk cs).IsZero
      · have head : c≠0 := by
          intro zero
          apply nonzero
          intro i
          cases i with
          | zero => exact zero
          | succ i => exact tail i
        refine ⟨0,?_,head⟩
        intro i hi
        cases i with
        | zero => omega
        | succ i => exact tail i
      · obtain ⟨d,degree,entry⟩:=ih tail
        refine ⟨d+1,?_,entry⟩
        intro i hi
        cases i with
        | zero => omega
        | succ i => exact degree i (by omega)

/-- Every nonzero formal divisor admits division with a strictly lower-degree
remainder. The divisor's actual leading position is constructed, not supplied. -/
theorem polynomial_division_exists (p q : Poly K) (nonzero : ¬q.IsZero) :
    ∃ d : Nat,∃ quotient remainder : Poly K,
      q.DegLt (d+1) ∧ q.coeff d≠0 ∧ remainder.DegLt d ∧
      PolynomialCoeffEq p (quotient*q+remainder) := by
  obtain ⟨d,degree,leading⟩:=leading_exists q nonzero
  obtain ⟨a,r,ad,rd,equation⟩:=polynomial_division_bounded q d p.coeffs.length degree leading p
    (Poly.DegLt.mono (Poly.degLt_length p) (by omega))
  exact ⟨d,a,r,degree,leading,rd,equation⟩
end NearCompression
