import NearCompression.PolynomialBezoutExistence

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]
local instance : NatCast K := Semiring.natCast

/-- Nonzero, nonconstant polynomial with no factorization into two
nonconstant polynomials, all interpreted coefficientwise. -/
def PolynomialIrreducible (p : Poly K) : Prop :=
  ¬p.IsZero ∧ ¬p.DegLt 1 ∧ ∀ a b : Poly K,
    PolynomialCoeffEq p (a*b)→a.DegLt 1 ∨ b.DegLt 1

private theorem constant_product (c : K) (q : Poly K) (i : Nat) :
    (Poly.C c*q).coeff i=c*q.coeff i := by
  change (Poly.smul c q+Poly.mk [0]).coeff i=_
  rw [Poly.coeff_add,Poly.coeff_smul]
  have zero : (Poly.mk [0] : Poly K).coeff i=0 := by cases i <;> simp [Poly.coeff,List.getD]
  rw [zero];grind

private theorem constant_coefficients (p : Poly K) (degree : p.DegLt 1) :
    PolynomialCoeffEq p (Poly.C (p.coeff 0)) := by
  intro i
  cases i with
  | zero => rfl
  | succ i => rw [degree (i+1) (by omega)];simp [Poly.C,Poly.coeff,List.getD]

/-- Low-degree irreducibility supplies, rather than assumes, a unit Bezout
certificate against the derivative. Irreducible-factor existence is separate. -/
theorem irreducible_derivative_bezout (characteristic : Nat) [IsCharP K characteristic]
    (p : Poly K) (d : Nat) (irreducible : PolynomialIrreducible p)
    (degree : p.DegLt (d+1)) (leading : p.coeff d≠0)
    (positive : 0<d) (small : d<characteristic) :
    ∃ A B : Poly K,PolynomialCoeffEq (A*p+B*polynomialDerivative p) (Poly.C 1) := by
  have scalar : (Nat.cast d : K)≠0 := by
    intro zero
    have h:=(IsCharP.natCast_eq_zero_iff characteristic d).mp zero
    rw [Nat.mod_eq_of_lt small] at h
    omega
  have derivativeNonzero : ¬(polynomialDerivative p).IsZero := by
    intro zero
    have entry:=zero (d-1)
    rw [polynomial_derivative_coefficient] at entry
    have equal : d-1+1=d := by omega
    rw [equal] at entry
    rcases Field.of_mul_eq_zero entry with cast|coefficient
    · exact scalar cast
    · exact leading coefficient
  obtain ⟨g,U,V,gnz,gd,identity,gderiv,gp⟩:=polynomial_bezout_gcd_exists d
    (polynomialDerivative p) p derivativeNonzero (polynomial_derivative_degree p d degree)
  obtain ⟨factor,division⟩:=gp
  have constant : g.DegLt 1 := by
    rcases irreducible.2.2 factor g division with factorConstant|gConstant
    · have equal:=polynomial_mul_congr factor (Poly.C (factor.coeff 0)) g g
        (constant_coefficients factor factorConstant) (fun _=>rfl) d
      have entry:=division d
      rw [equal,constant_product,gd d (Nat.le_refl d)] at entry
      apply False.elim
      exact leading (by grind)
    · exact gConstant
  have value : g.coeff 0≠0 := by
    intro zero
    apply gnz
    intro i
    cases i with
    | zero => exact zero
    | succ i => exact constant (i+1) (by omega)
  refine ⟨Poly.C ((g.coeff 0)⁻¹)*V,Poly.C ((g.coeff 0)⁻¹)*U,?_⟩
  intro i
  rw [Poly.coeff_add,polynomial_mul_assoc,constant_product,polynomial_mul_assoc,constant_product]
  have h:=identity i
  rw [Poly.coeff_add] at h
  have inverse:=Field.mul_inv_cancel value
  cases i with
  | zero => change (g.coeff 0)⁻¹*(V*p).coeff 0+(g.coeff 0)⁻¹*(U*polynomialDerivative p).coeff 0=1;grind
  | succ i =>
    have zero:=constant (i+1) (by omega)
    have one : (Poly.C (1:K)).coeff (i+1)=0 := by simp [Poly.C,Poly.coeff,List.getD]
    rw [one]
    grind

/-- Every existing root of an irreducible polynomial of degree below the
characteristic is smooth. This does not assert that a root exists in K. -/
theorem irreducible_small_degree_root_smooth (characteristic : Nat) [IsCharP K characteristic]
    (p : Poly K) (d : Nat) (irreducible : PolynomialIrreducible p)
    (degree : p.DegLt (d+1)) (leading : p.coeff d≠0)
    (positive : 0<d) (small : d<characteristic) (a : K) (root : p.eval a=0) :
    (polynomialDerivative p).eval a≠0 := by
  obtain ⟨A,B,certificate⟩:=irreducible_derivative_bezout characteristic p d irreducible degree leading positive small
  exact bezout_no_common_root p (polynomialDerivative p) A B 1 a certificate
    (fun zero=>Field.zero_ne_one zero.symm) root
end NearCompression
