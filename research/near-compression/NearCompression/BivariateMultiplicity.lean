import NearCompression.MultipointMultiplicity

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- A lower degree bound: all coefficients strictly below m vanish. -/
def PolynomialOrder (p : Poly K) (m : Nat) : Prop := ∀ i<m,p.coeff i=0

private theorem order_add (p q : Poly K) (m : Nat)
    (hp : PolynomialOrder p m) (hq : PolynomialOrder q m) : PolynomialOrder (p+q) m := by
  intro i hi
  rw [Poly.coeff_add,hp i hi,hq i hi]
  grind

private theorem order_scale (p : Poly K) (c : K) (m : Nat)
    (hp : PolynomialOrder p m) : PolynomialOrder (Poly.smul c p) m := by
  intro i hi
  rw [Poly.coeff_smul,hp i hi]
  grind

private theorem order_cons_same (cs : List K) (m : Nat)
    (h : PolynomialOrder (Poly.mk cs) m) : PolynomialOrder (Poly.mk (0::cs)) m := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i => exact h i (by omega)

/-- Multiplication adds lower degree bounds, without any degree/field-size
restriction and without treating polynomial functions as formal polynomials. -/
theorem polynomial_order_mul (m n : Nat) (p q : Poly K)
    (hp : PolynomialOrder p m) (hq : PolynomialOrder q n) : PolynomialOrder (p*q) (m+n) := by
  induction m generalizing p with
  | zero =>
    cases p with
    | mk cs =>
      induction cs with
      | nil => intro i hi;simp [Poly.coeff,Poly.mulL]
      | cons c cs ih =>
        change PolynomialOrder (Poly.smul c q+Poly.mk (0::Poly.mulL cs q.coeffs)) (0+n)
        simp only [Nat.zero_add] at ih ⊢
        apply order_add
        · exact order_scale q c n hq
        · exact order_cons_same _ n (ih (by intro i hi;omega))
  | succ m ih =>
    cases p with
    | mk cs =>
      cases cs with
      | nil => intro i hi;simp [Poly.coeff,Poly.mulL]
      | cons c cs =>
        have hc : c=0 := hp 0 (by omega)
        have tail : PolynomialOrder (Poly.mk cs) m := fun i hi=>hp (i+1) (by omega)
        have product:=ih (Poly.mk cs) tail
        change PolynomialOrder (Poly.smul c q+Poly.mk (0::Poly.mulL cs q.coeffs)) (m+1+n)
        apply order_add
        · intro i hi;rw [Poly.coeff_smul,hc];grind
        · intro i hi
          cases i with
          | zero => rfl
          | succ i => exact product i (by omega)

/-- At zero, synthetic jets are exactly the formal coefficients. -/
theorem synthetic_jet_zero (p : Poly K) (i : Nat) : syntheticJet p 0 i=p.coeff i := by
  induction i generalizing p with
  | zero =>
    cases p with
    | mk cs => cases cs <;> simp [syntheticJet,Poly.eval,Poly.evalL,Poly.coeff] <;> grind
  | succ i ih =>
    change syntheticJet (p.quot 0) 0 i=p.coeff (i+1)
    rw [ih,synthetic_quotient_tail]
    have h : ∀ cs : List K,Poly.evalL 0 cs=cs.getD 0 0 := by
      intro cs;cases cs <;> simp [Poly.evalL] <;> grind
    change Poly.evalL 0 (p.coeffs.drop (i+1))=p.coeffs.getD (i+1) 0
    rw [h]
    simp [List.getD,List.getElem?_drop]

/-- Rows are polynomials in X, ordered by powers of Y. -/
def bivariateSubstitute : List (Poly K)→Poly K→Poly K
  | [],_ => Poly.zero
  | row::rest,curve => row+curve*bivariateSubstitute rest curve

/-- Formal mixed coefficients of total degree below m vanish at (0,0).
Rows may contain trailing zeros; missing rows are the zero polynomial. -/
def BivariateOrder (rows : List (Poly K)) (m : Nat) : Prop :=
  ∀ i j,i+j<m→(rows.getD j Poly.zero).coeff i=0

/-- Centered bivariate substitution preserves total-order multiplicity for
ANY curve through (0,0), not only an affine curve. -/
theorem bivariate_substitution_order (m : Nat) (rows : List (Poly K)) (curve : Poly K)
    (through : curve.coeff 0=0) (mixed : BivariateOrder rows m) :
    PolynomialOrder (bivariateSubstitute rows curve) m := by
  induction rows generalizing m with
  | nil => intro i hi;simp [bivariateSubstitute,Poly.zero,Poly.coeff]
  | cons row rest ih =>
    cases m with
    | zero => intro i hi;omega
    | succ m =>
      have head : PolynomialOrder row (m+1) := fun i hi=>mixed i 0 (by omega)
      have tail : BivariateOrder rest m := by
        intro i j hij
        exact mixed i (j+1) (by omega)
      have low : PolynomialOrder curve 1 := by
        intro i hi
        have zero : i=0 := by omega
        simpa only [zero] using through
      have product:=polynomial_order_mul 1 m curve (bivariateSubstitute rest curve) low (ih m tail)
      exact order_add row _ (m+1) head (by simpa only [Nat.add_comm] using product)

/-- Operational jet form of the centered substitution theorem, ready for
the independent multi-point bound once translation identities are supplied. -/
theorem bivariate_substitution_jets (m : Nat) (rows : List (Poly K)) (curve : Poly K)
    (through : curve.coeff 0=0) (mixed : BivariateOrder rows m) :
    ∀ i<m,syntheticJet (bivariateSubstitute rows curve) 0 i=0 := by
  intro i hi
  rw [synthetic_jet_zero]
  exact bivariate_substitution_order m rows curve through mixed i hi
end NearCompression
