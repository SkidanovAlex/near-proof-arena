import NearCompression.BivariateMultiplicity

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem product_cons (c : K) (cs : List K) (q : Poly K) (i : Nat) :
    ((Poly.mk (c::cs))*q).coeff i=c*q.coeff i+
      (match i with | 0=>0 | j+1=>((Poly.mk cs)*q).coeff j) := by
  change (Poly.smul c q+Poly.mk (0::Poly.mulL cs q.coeffs)).coeff i=_
  rw [Poly.coeff_add,Poly.coeff_smul]
  cases i <;> rfl

/-- The first potentially nonzero product coefficient is the product of the
first potentially nonzero input coefficients. All characteristics allowed. -/
theorem polynomial_order_product_coefficient (p q : Poly K) (m n : Nat)
    (hp : PolynomialOrder p m) (hq : PolynomialOrder q n) :
    (p*q).coeff (m+n)=p.coeff m*q.coeff n := by
  induction m generalizing p with
  | zero =>
    simp only [Nat.zero_add]
    cases p with
    | mk cs =>
      cases cs with
      | nil => simp [Poly.coeff,Poly.mulL];grind
      | cons c cs =>
        rw [product_cons]
        cases n with
        | zero => change c*q.coeff 0+0=c*q.coeff 0;grind
        | succ n =>
          have tail:=polynomial_order_mul 0 (n+1) (Poly.mk cs) q
            (by intro i hi;omega) hq
          have vanish:=tail n (by omega)
          change c*q.coeff (n+1)+((Poly.mk cs)*q).coeff n=c*q.coeff (n+1)
          rw [vanish];grind
  | succ m ih =>
    cases p with
    | mk cs =>
      cases cs with
      | nil => simp [Poly.coeff,Poly.mulL];grind
      | cons c cs =>
        have head : c=0 := hp 0 (by omega)
        have tail : PolynomialOrder (Poly.mk cs) m := fun i hi=>hp (i+1) (by omega)
        rw [product_cons,head]
        have step:=ih (Poly.mk cs) tail
        have index : m+1+n=(m+n)+1 := by omega
        simp only [index]
        change 0*q.coeff (m+n+1)+((Poly.mk cs)*q).coeff (m+n)=
          (Poly.mk cs).coeff m*q.coeff n
        rw [step];grind

private theorem first_nonzero (p : Poly K) (nonzero : ¬p.IsZero) :
    ∃ m,PolynomialOrder p m ∧ p.coeff m≠0 := by
  cases p with
  | mk cs =>
    induction cs with
    | nil => exact False.elim (nonzero (by intro i;simp [Poly.coeff]))
    | cons c cs ih =>
      by_cases head : c=0
      · have tail : ¬(Poly.mk cs).IsZero := by
          intro zero
          apply nonzero
          intro i
          cases i with
          | zero => exact head
          | succ i => exact zero i
        obtain ⟨m,order,nz⟩:=ih tail
        refine ⟨m+1,?_,nz⟩
        intro i hi
        cases i with
        | zero => exact head
        | succ i => exact order i (by omega)
      · exact ⟨0,(by intro i hi;omega),head⟩

/-- Nonzero formal polynomials have nonzero product, including over finite
fields where nonzero polynomials can vanish at every evaluation point. -/
theorem polynomial_product_nonzero (p q : Poly K)
    (hp : ¬p.IsZero) (hq : ¬q.IsZero) : ¬(p*q).IsZero := by
  obtain ⟨m,pm,pnz⟩:=first_nonzero p hp
  obtain ⟨n,qn,qnz⟩:=first_nonzero q hq
  intro zero
  have coefficient:=zero (m+n)
  rw [polynomial_order_product_coefficient p q m n pm qn] at coefficient
  rcases Field.of_mul_eq_zero coefficient with h|h
  · exact pnz h
  · exact qnz h

/-- Formal zero-product cancellation; no sampled evaluation premise. -/
theorem polynomial_product_zero_iff (p q : Poly K) :
    (p*q).IsZero ↔ p.IsZero ∨ q.IsZero := by
  constructor
  · intro product
    by_cases hp : p.IsZero
    · exact Or.inl hp
    · apply Or.inr
      apply Classical.byContradiction
      intro hq
      exact polynomial_product_nonzero p q hp hq product
  · intro zero i
    rcases zero with hp|hq
    · exact polynomial_order_mul (i+1) 0 p q (fun j _=>hp j)
        (by intro j hj;omega) i (by omega)
    · exact polynomial_order_mul 0 (i+1) p q (by intro j hj;omega)
        (fun j _=>hq j) i (by omega)
end NearCompression
