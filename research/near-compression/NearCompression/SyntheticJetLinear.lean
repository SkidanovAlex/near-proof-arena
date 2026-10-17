import NearCompression.GSMonomialSpace

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def PolynomialCoeffEq (p q : Poly K) : Prop := ∀ i,p.coeff i=q.coeff i

private theorem coeff_eq_eval (p q : Poly K) (equal : PolynomialCoeffEq p q) (a : K) : p.eval a=q.eval a := by
  have zero : (p-q).IsZero := by
    intro i;rw [Poly.coeff_sub,equal i];grind
  have h:=Poly.eval_of_isZero zero a
  rw [Poly.eval_sub] at h
  grind

private theorem tail_coefficient (p : Poly K) (n i : Nat) :
    (Poly.mk (p.coeffs.drop n)).coeff i=p.coeff (n+i) := by
  simp [Poly.coeff,List.getD,List.getElem?_drop]

private theorem quotient_congr (p q : Poly K) (equal : PolynomialCoeffEq p q) (a : K) :
    PolynomialCoeffEq (p.quot a) (q.quot a) := by
  intro i
  rw [synthetic_quotient_tail,synthetic_quotient_tail]
  apply coeff_eq_eval
  intro j
  rw [tail_coefficient,tail_coefficient,equal]

private theorem quotient_add (p q : Poly K) (a : K) :
    PolynomialCoeffEq ((p+q).quot a) (p.quot a+q.quot a) := by
  intro i
  rw [Poly.coeff_add,synthetic_quotient_tail,synthetic_quotient_tail,synthetic_quotient_tail]
  rw [←Poly.eval_add]
  apply coeff_eq_eval
  intro j
  rw [tail_coefficient,Poly.coeff_add,Poly.coeff_add,tail_coefficient,tail_coefficient]

private theorem quotient_scale (p : Poly K) (c a : K) :
    PolynomialCoeffEq ((Poly.smul c p).quot a) (Poly.smul c (p.quot a)) := by
  intro i
  rw [Poly.coeff_smul,synthetic_quotient_tail,synthetic_quotient_tail]
  rw [←Poly.eval_smul]
  apply coeff_eq_eval
  intro j
  rw [tail_coefficient,Poly.coeff_smul,Poly.coeff_smul,tail_coefficient]

/-- Jets respect formal coefficient equality even with different zero padding. -/
theorem synthetic_jet_congr (p q : Poly K) (equal : PolynomialCoeffEq p q) (a : K) (i : Nat) :
    syntheticJet p a i=syntheticJet q a i := by
  induction i generalizing p q with
  | zero => exact coeff_eq_eval p q equal a
  | succ i ih => exact ih (p.quot a) (q.quot a) (quotient_congr p q equal a)

theorem synthetic_jet_add (p q : Poly K) (a : K) (i : Nat) :
    syntheticJet (p+q) a i=syntheticJet p a i+syntheticJet q a i := by
  induction i generalizing p q with
  | zero => exact Poly.eval_add p q a
  | succ i ih =>
    change syntheticJet ((p+q).quot a) a i=syntheticJet (p.quot a) a i+syntheticJet (q.quot a) a i
    rw [synthetic_jet_congr _ _ (quotient_add p q a) a i,ih]

theorem synthetic_jet_scale (p : Poly K) (c a : K) (i : Nat) :
    syntheticJet (Poly.smul c p) a i=c*syntheticJet p a i := by
  induction i generalizing p with
  | zero => exact Poly.eval_smul c p a
  | succ i ih =>
    change syntheticJet ((Poly.smul c p).quot a) a i=c*syntheticJet (p.quot a) a i
    rw [synthetic_jet_congr _ _ (quotient_scale p c a) a i,ih]

private theorem zero_jet (a : K) (i : Nat) : syntheticJet (Poly.zero : Poly K) a i=0 := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih

/-- A finite polynomial linear combination commutes with every jet. -/
theorem synthetic_jet_sum (ps : List (Poly K)) (a : K) (i : Nat) :
    syntheticJet (Poly.sum ps) a i=(ps.map (fun p=>syntheticJet p a i)).foldr (·+·) 0 := by
  induction ps with
  | nil => exact zero_jet a i
  | cons p rest ih =>
    change syntheticJet (p+Poly.sum rest) a i=syntheticJet p a i+
      (rest.map (fun q=>syntheticJet q a i)).foldr (·+·) 0
    rw [synthetic_jet_add,ih]

/-- Translation is coefficient-linear; its stored lengths need not match. -/
theorem polynomial_translate_linear (p q : Poly K) (c a : K) :
    PolynomialCoeffEq (polynomialTranslate (p+Poly.smul c q) a)
      (polynomialTranslate p a+Poly.smul c (polynomialTranslate q a)) := by
  intro i
  rw [Poly.coeff_add,Poly.coeff_smul,polynomial_translate_coeff,polynomial_translate_coeff,
    polynomial_translate_coeff,synthetic_jet_add,synthetic_jet_scale]
end NearCompression
