import NearCompression.RegularPolynomialDivision

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- List specialization supplies values at every coefficient, including zeros
past the end of the represented polynomial. -/
theorem rational_polynomial_specializes_coefficient (p : Poly (PolynomialRational K)) (q : Poly K)
    (z : K) (specializes : RationalPolynomialSpecializes p q z) (i : Nat) :
    PolynomialRationalValueAt (p.coeff i) z (q.coeff i) := by
  cases p with | mk ps => cases q with | mk qs =>
    change RationalCoefficientSpecialization z ps qs at specializes
    induction specializes generalizing i with
    | nil => exact rational_coefficient_specializes 0 z
    | @cons r c rs cs head tail ih => cases i with
      | zero => exact head
      | succ i => exact ih i

theorem rational_polynomial_specializes_regular (p : Poly (PolynomialRational K)) (q : Poly K)
    (z : K) (specializes : RationalPolynomialSpecializes p q z) : RationalPolynomialRegularAt p z :=
  fun i=>⟨q.coeff i,rational_polynomial_specializes_coefficient p q z specializes i⟩

/-- Equivalent regular representatives agree at a specialized modulus root.
The specialized leading coefficient must remain nonzero; the regular quotient
is constructed rather than assumed for the congruence witness. -/
theorem algebraic_regular_representative_value_eq
    (h p q : Poly (PolynomialRational K)) (hs ps qs : Poly K) (d : Nat) (z a : K)
    (hd : h.DegLt (d+1)) (hl : h.coeff d≠0)
    (hsp : RationalPolynomialSpecializes h hs z) (leadingSafe : hs.coeff d≠0)
    (psp : RationalPolynomialSpecializes p ps z) (qsp : RationalPolynomialSpecializes q qs z)
    (same : PolynomialResidueEq h p q) (root : hs.eval a=0) : ps.eval a=qs.eval a := by
  have hr:=rational_polynomial_specializes_regular h hs z hsp
  have pr:=rational_polynomial_specializes_regular p ps z psp
  have qr:=rational_polynomial_specializes_regular q qs z qsp
  obtain ⟨t,tr,identity⟩:=rational_polynomial_regular_exact_quotient (p-q) h d z (hs.coeff d)
    hd hl hr (rational_polynomial_regular_sub p q z pr qr)
    (rational_polynomial_specializes_coefficient h hs z hsp d) leadingSafe same
  obtain ⟨ts,tsp⟩:=rational_polynomial_specialization_exists t z tr
  have reconstructed : PolynomialCoeffEq p (q+t*h) := by
    intro i
    have entry:=identity i
    rw [Poly.coeff_sub] at entry
    rw [Poly.coeff_add];grind
  have evaluated:=synthetic_jet_congr p (q+t*h) reconstructed (polynomialRationalCoefficientMap.toFun a) 0
  change p.eval _=(q+t*h).eval _ at evaluated
  rw [Poly.eval_add,Poly.eval_mul] at evaluated
  have right:=polynomial_rational_value_add _ _ z _ _ (rational_polynomial_eval_specializes q qs z a qsp)
    (polynomial_rational_value_mul _ _ z _ _ (rational_polynomial_eval_specializes t ts z a tsp)
      (rational_polynomial_eval_specializes h hs z a hsp))
  rw [←evaluated] at right
  have numeric:=polynomial_rational_value_unique _ z _ _
    (rational_polynomial_eval_specializes p ps z a psp) right
  rw [root] at numeric
  grind

/-- Partial evaluation of an algebraic residue at a parameter point and a
chosen specialized modulus root. Only regular representatives are witnesses. -/
def AlgebraicResidueValueAt (h : Poly (PolynomialRational K)) (x : PolynomialResidue h)
    (z a value : K) : Prop :=
  ∃ p : Poly (PolynomialRational K),∃ q : Poly K,
    polynomialResidueClass h p=x ∧ RationalPolynomialSpecializes p q z ∧ q.eval a=value

/-- Partial specialization is well-defined on the quotient, despite having
many polynomial representatives and possible poles outside its domain. -/
theorem algebraic_residue_value_unique (h : Poly (PolynomialRational K)) (hs : Poly K)
    (d : Nat) (z a : K) (hd : h.DegLt (d+1)) (hl : h.coeff d≠0)
    (hsp : RationalPolynomialSpecializes h hs z) (leadingSafe : hs.coeff d≠0)
    (root : hs.eval a=0) (x : PolynomialResidue h) (u v : K)
    (hu : AlgebraicResidueValueAt h x z a u) (hv : AlgebraicResidueValueAt h x z a v) : u=v := by
  obtain ⟨p,ps,px,psp,pu⟩:=hu
  obtain ⟨q,qs,qx,qsp,qv⟩:=hv
  have same:=(polynomial_residue_class_eq_iff h p q).mp (px.trans qx.symm)
  exact pu.symm.trans ((algebraic_regular_representative_value_eq h p q hs ps qs d z a hd hl
    hsp leadingSafe psp qsp same root).trans qv)

/-- Addition preserves the domain and value of partial residue specialization. -/
theorem algebraic_residue_value_add (h : Poly (PolynomialRational K)) (x y : PolynomialResidue h)
    (z a u v : K) (hx : AlgebraicResidueValueAt h x z a u) (hy : AlgebraicResidueValueAt h y z a v) :
    AlgebraicResidueValueAt h (polynomialResidueAdd h x y) z a (u+v) := by
  obtain ⟨p,ps,px,psp,pu⟩:=hx
  obtain ⟨q,qs,qy,qsp,qv⟩:=hy
  obtain ⟨rs,rsp⟩:=rational_polynomial_specialization_exists (p+q) z
    (rational_polynomial_regular_add p q z (rational_polynomial_specializes_regular p ps z psp)
      (rational_polynomial_specializes_regular q qs z qsp))
  refine ⟨p+q,rs,?_,rsp,?_⟩
  · rw [←px,←qy];rfl
  · have actual:=rational_polynomial_eval_specializes (p+q) rs z a rsp
    rw [Poly.eval_add] at actual
    have expected:=polynomial_rational_value_add _ _ z _ _
      (rational_polynomial_eval_specializes p ps z a psp) (rational_polynomial_eval_specializes q qs z a qsp)
    have equal:=polynomial_rational_value_unique _ z _ _ actual expected
    rwa [pu,qv] at equal

/-- Multiplication likewise preserves the partial specialization domain. -/
theorem algebraic_residue_value_mul (h : Poly (PolynomialRational K)) (x y : PolynomialResidue h)
    (z a u v : K) (hx : AlgebraicResidueValueAt h x z a u) (hy : AlgebraicResidueValueAt h y z a v) :
    AlgebraicResidueValueAt h (polynomialResidueMul h x y) z a (u*v) := by
  obtain ⟨p,ps,px,psp,pu⟩:=hx
  obtain ⟨q,qs,qy,qsp,qv⟩:=hy
  obtain ⟨rs,rsp⟩:=rational_polynomial_specialization_exists (p*q) z
    (rational_polynomial_regular_mul p q z (rational_polynomial_specializes_regular p ps z psp)
      (rational_polynomial_specializes_regular q qs z qsp))
  refine ⟨p*q,rs,?_,rsp,?_⟩
  · rw [←px,←qy];rfl
  · have actual:=rational_polynomial_eval_specializes (p*q) rs z a rsp
    rw [Poly.eval_mul] at actual
    have expected:=polynomial_rational_value_mul _ _ z _ _
      (rational_polynomial_eval_specializes p ps z a psp) (rational_polynomial_eval_specializes q qs z a qsp)
    have equal:=polynomial_rational_value_unique _ z _ _ actual expected
    rwa [pu,qv] at equal
end NearCompression
