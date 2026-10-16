import NearCompression.PolynomialFactorization

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem constant_product (c : K) (q : Poly K) (i : Nat) :
    (Poly.C c*q).coeff i=c*q.coeff i := by
  change (Poly.smul c q+Poly.mk [0]).coeff i=_
  rw [Poly.coeff_add,Poly.coeff_smul]
  have zero : (Poly.mk [0] : Poly K).coeff i=0 := by cases i <;> rfl
  rw [zero];grind

private theorem constant_coefficients (p : Poly K) (degree : p.DegLt 1) :
    PolynomialCoeffEq p (Poly.C (p.coeff 0)) := by
  intro i
  cases i with | zero => rfl | succ i => exact degree (i+1) (by omega)

/-- Every nonzero polynomial below an irreducible modulus's degree has a
unit Bezout certificate with that modulus. No characteristic bound is needed. -/
theorem irreducible_bounded_residue_bezout (h r : Poly K) (d : Nat)
    (irreducible : PolynomialIrreducible h) (leading : h.coeff d≠0)
    (degree : r.DegLt d) (nonzero : ¬r.IsZero) :
    ∃ A B : Poly K, PolynomialCoeffEq (A*r+B*h) (Poly.C 1) := by
  obtain ⟨g,U,V,gnz,gd,identity,_,gh⟩:=polynomial_bezout_gcd_exists d r h nonzero degree
  obtain ⟨factor,division⟩:=gh
  have constant : g.DegLt 1 := by
    rcases irreducible.2.2 factor g division with fc|gc
    · have equal:=polynomial_mul_congr factor (Poly.C (factor.coeff 0)) g g
        (constant_coefficients factor fc) (fun _=>rfl) d
      have entry:=division d
      rw [equal,constant_product,gd d (Nat.le_refl d)] at entry
      exact False.elim (leading (by grind))
    · exact gc
  have value : g.coeff 0≠0 := by
    intro zero;apply gnz;intro i
    cases i with | zero => exact zero | succ i => exact constant (i+1) (by omega)
  refine ⟨Poly.C ((g.coeff 0)⁻¹)*U,Poly.C ((g.coeff 0)⁻¹)*V,?_⟩
  intro i
  rw [Poly.coeff_add,polynomial_mul_assoc,constant_product,polynomial_mul_assoc,constant_product]
  have entry:=identity i
  rw [Poly.coeff_add] at entry
  have inverse:=Field.mul_inv_cancel value
  cases i with
  | zero => change (g.coeff 0)⁻¹*(U*r).coeff 0+(g.coeff 0)⁻¹*(V*h).coeff 0=1;grind
  | succ i =>
    have zero:=constant (i+1) (by omega)
    have one : (Poly.C (1:K)).coeff (i+1)=0 := by cases i <;> rfl
    rw [one];grind

private theorem mul_sub (p q r : Poly K) : PolynomialCoeffEq (p*(q-r)) (p*q-p*r) := by
  intro i
  rw [polynomial_mul_comm p (q-r),polynomial_sub_mul,Poly.coeff_sub,Poly.coeff_sub,
    polynomial_mul_comm q p,polynomial_mul_comm r p]

/-- Any representative not divisible by the irreducible modulus is coprime
to it. The division and Euclidean witnesses are constructed in the proof. -/
theorem irreducible_nondivisible_bezout (h p : Poly K)
    (irreducible : PolynomialIrreducible h) (nonzero : ¬PolynomialDivides h p) :
    ∃ A B : Poly K, PolynomialCoeffEq (A*p+B*h) (Poly.C 1) := by
  obtain ⟨d,t,r,_,leading,rd,division⟩:=polynomial_division_exists p h irreducible.1
  have rn : ¬r.IsZero := by
    intro zero;apply nonzero;refine ⟨t,?_⟩;intro i
    have entry:=division i
    rw [Poly.coeff_add,zero i] at entry
    grind
  obtain ⟨A,B,certificate⟩:=irreducible_bounded_residue_bezout h r d irreducible leading rd rn
  have remainder : PolynomialCoeffEq r (p-t*h) := by
    intro i;have entry:=division i;rw [Poly.coeff_add] at entry
    rw [Poly.coeff_sub];grind
  refine ⟨A,B-A*t,?_⟩
  intro i
  have through:=polynomial_mul_congr A A r (p-t*h) (fun _=>rfl) remainder i
  rw [mul_sub,Poly.coeff_sub,←polynomial_mul_assoc] at through
  have entry:=certificate i
  rw [Poly.coeff_add,through] at entry
  rw [Poly.coeff_add,polynomial_sub_mul,Poly.coeff_sub]
  grind

/-- Congruence modulo a polynomial is formal divisibility of the difference. -/
def PolynomialResidueEq (h p q : Poly K) : Prop := PolynomialDivides h (p-q)

/-- Every nonzero residue class modulo an irreducible has an inverse,
represented by a polynomial of degree strictly below the modulus. -/
theorem irreducible_residue_inverse (h p : Poly K) (d : Nat)
    (irreducible : PolynomialIrreducible h) (hd : h.DegLt (d+1))
    (leading : h.coeff d≠0) (nonzero : ¬PolynomialDivides h p) :
    ∃ inverse : Poly K, inverse.DegLt d ∧ PolynomialResidueEq h (inverse*p) (Poly.C 1) := by
  obtain ⟨A,B,certificate⟩:=irreducible_nondivisible_bezout h p irreducible nonzero
  obtain ⟨t,r,_,rd,division⟩:=polynomial_division_bounded h d A.coeffs.length hd leading A
    (Poly.DegLt.mono (Poly.degLt_length A) (by omega))
  refine ⟨r,rd,Poly.C (-1)*(t*p+B),?_⟩
  intro i
  have through:=polynomial_mul_congr A (t*h+r) p p division (fun _=>rfl) i
  rw [polynomial_add_mul,Poly.coeff_add,polynomial_mul_assoc,
    polynomial_mul_congr t t (h*p) (p*h) (fun _=>rfl) (polynomial_mul_comm h p),
    ←polynomial_mul_assoc] at through
  have entry:=certificate i
  rw [Poly.coeff_add,through] at entry
  rw [Poly.coeff_sub,polynomial_mul_assoc,constant_product,polynomial_add_mul,Poly.coeff_add]
  grind

/-- Polynomial division supplies a reduced representative of every class. -/
theorem polynomial_residue_representative (h p : Poly K) (d : Nat)
    (hd : h.DegLt (d+1)) (leading : h.coeff d≠0) :
    ∃ r : Poly K, r.DegLt d ∧ PolynomialResidueEq h p r := by
  obtain ⟨t,r,_,rd,division⟩:=polynomial_division_bounded h d p.coeffs.length hd leading p
    (Poly.DegLt.mono (Poly.degLt_length p) (by omega))
  refine ⟨r,rd,t,?_⟩
  intro i
  have entry:=division i
  rw [Poly.coeff_add] at entry
  rw [Poly.coeff_sub];grind

/-- Two reduced representatives of the same residue are coefficientwise
identical. List padding is deliberately not treated as distinct field elements. -/
theorem polynomial_reduced_residue_unique (h a b : Poly K) (d : Nat)
    (leading : h.coeff d≠0) (ad : a.DegLt d) (bd : b.DegLt d)
    (same : PolynomialResidueEq h a b) : PolynomialCoeffEq a b := by
  have zero : (a-b).IsZero := by
    apply Classical.byContradiction
    intro nonzero
    have impossible:=polynomial_divisor_degree (a-b) h d nonzero (Poly.degLt_sub ad bd) same
    exact leading (impossible d (Nat.le_refl d))
  intro i
  have entry:=zero i
  rw [Poly.coeff_sub] at entry
  grind

/-- Nonzero base-field constants stay nonzero modulo any irreducible modulus. -/
theorem irreducible_residue_constant_nonzero (h : Poly K) (c : K)
    (irreducible : PolynomialIrreducible h) (nonzero : c≠0) :
    ¬PolynomialDivides h (Poly.C c) := by
  intro divides
  have cn : ¬(Poly.C c).IsZero := fun zero=>nonzero (zero 0)
  exact irreducible.2.1 (polynomial_divisor_degree (Poly.C c) h 1 cn (Poly.degLt_length _) divides)
end NearCompression
