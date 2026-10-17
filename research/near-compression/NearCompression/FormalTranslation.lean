import NearCompression.PolynomialCoefficientAlgebra
import NearCompression.MixedJetTranslation

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem zero_coeff (i : Nat) : (Poly.zero : Poly K).coeff i=0 := rfl
private theorem product_zero (p : Poly K) (i : Nat) : (p*Poly.zero).coeff i=0 := by
  exact polynomial_order_mul 0 (i+1) p Poly.zero (by intro j hj;omega) (by intro j hj;rfl) i (by omega)

private theorem cons_product (c : K) (cs : List K) (q : Poly K) (i : Nat) :
    ((Poly.mk (c::cs))*q).coeff i=c*q.coeff i+
      (match i with | 0=>0 | j+1=>((Poly.mk cs)*q).coeff j) := by
  change (Poly.smul c q+Poly.mk (0::Poly.mulL cs q.coeffs)).coeff i=_
  rw [Poly.coeff_add,Poly.coeff_smul]
  cases i <;> rfl

private theorem constant_product (c : K) (q : Poly K) (i : Nat) :
    ((Poly.C c)*q).coeff i=c*q.coeff i := by
  change ((Poly.mk (c::[]))*q).coeff i=_
  rw [cons_product]
  cases i <;> change c*q.coeff _+0=c*q.coeff _ <;> grind

private theorem affine_product (a : K) (p : Poly K) (i : Nat) :
    ((Poly.mk [a,1])*p).coeff i=a*p.coeff i+
      (match i with | 0=>0 | j+1=>p.coeff j) := by
  rw [cons_product]
  cases i with
  | zero => rfl
  | succ i =>
    change a*p.coeff (i+1)+(Poly.C 1*p).coeff i=a*p.coeff (i+1)+p.coeff i
    rw [constant_product];grind

private theorem translate_cons (c : K) (cs : List K) (a : K) :
    PolynomialCoeffEq (polynomialTranslate (Poly.mk (c::cs)) a)
      (Poly.C c+(Poly.mk [a,1])*polynomialTranslate (Poly.mk cs) a) := by
  intro i
  rw [Poly.coeff_add,affine_product,polynomial_translate_coeff]
  cases i with
  | zero =>
    rw [polynomial_translate_coeff]
    change c+a*(Poly.mk cs).eval a=c+(a*(Poly.mk cs).eval a+0)
    grind
  | succ i =>
    simp only [synthetic_jet_cons_succ,polynomial_translate_coeff]
    have constant : (Poly.C c).coeff (i+1)=0 := by simp [Poly.C,Poly.coeff,List.getD]
    rw [constant];grind

private theorem translate_add (p q : Poly K) (a : K) :
    PolynomialCoeffEq (polynomialTranslate (p+q) a)
      (polynomialTranslate p a+polynomialTranslate q a) := by
  intro i
  rw [Poly.coeff_add,polynomial_translate_coeff,polynomial_translate_coeff,
    polynomial_translate_coeff,synthetic_jet_add]

private theorem translate_scale (p : Poly K) (c a : K) :
    PolynomialCoeffEq (polynomialTranslate (Poly.smul c p) a)
      (Poly.smul c (polynomialTranslate p a)) := by
  intro i
  rw [Poly.coeff_smul,polynomial_translate_coeff,polynomial_translate_coeff,synthetic_jet_scale]

/-- Formal translation is multiplicative, including in small characteristic
and for polynomials whose degree exceeds the field size. -/
theorem polynomial_translate_mul (p q : Poly K) (a : K) :
    PolynomialCoeffEq (polynomialTranslate (p*q) a)
      (polynomialTranslate p a*polynomialTranslate q a) := by
  cases p with | mk ps =>
    induction ps with
    | nil => intro i;rfl
    | cons c cs ih =>
      intro i
      have right:=polynomial_mul_congr _ _ (polynomialTranslate q a) (polynomialTranslate q a)
        (translate_cons c cs a) (fun _=>rfl) i
      rw [right,polynomial_add_mul,Poly.coeff_add,constant_product,polynomial_mul_assoc]
      change (polynomialTranslate (Poly.smul c q+Poly.mk (0::Poly.mulL cs q.coeffs)) a).coeff i=_
      rw [translate_add,Poly.coeff_add,translate_scale,Poly.coeff_smul,translate_cons,Poly.coeff_add]
      have through:=polynomial_mul_congr (Poly.mk [a,1]) (Poly.mk [a,1]) _ _ (fun _=>rfl) ih i
      change c*(polynomialTranslate q a).coeff i+((Poly.C 0).coeff i+
        ((Poly.mk [a,1])*polynomialTranslate ((Poly.mk cs)*q) a).coeff i)=_
      rw [through]
      have constant : (Poly.C (0:K)).coeff i=0 := by cases i <;> simp [Poly.C,Poly.coeff,List.getD]
      rw [constant];grind
private theorem swap (p q r : Poly K) : PolynomialCoeffEq (p*(q*r)) (q*(p*r)) := by
  intro i
  rw [←polynomial_mul_assoc,←polynomial_mul_assoc]
  exact polynomial_mul_congr (p*q) (q*p) r r (polynomial_mul_comm p q) (fun _=>rfl) i

private theorem substitute_add (xs ys : List (Poly K)) (curve : Poly K) :
    PolynomialCoeffEq (bivariateSubstitute (bivariateAddRows xs ys) curve)
      (bivariateSubstitute xs curve+bivariateSubstitute ys curve) := by
  induction xs generalizing ys with
  | nil => intro i;rw [Poly.coeff_add];change (bivariateSubstitute ys curve).coeff i=0+(bivariateSubstitute ys curve).coeff i;grind
  | cons x xs ih =>
    cases ys with
    | nil => intro i;rw [Poly.coeff_add];change (bivariateSubstitute (x::xs) curve).coeff i=(bivariateSubstitute (x::xs) curve).coeff i+0;grind
    | cons y ys =>
      intro i
      have through:=polynomial_mul_congr curve curve _ _ (fun _=>rfl) (ih ys) i
      change ((x+y)+curve*bivariateSubstitute (bivariateAddRows xs ys) curve).coeff i=_
      rw [Poly.coeff_add,Poly.coeff_add,through,polynomial_mul_add,Poly.coeff_add]
      simp only [bivariateSubstitute,Poly.coeff_add]
      grind

private theorem substitute_scale (rows : List (Poly K)) (b : K) (curve : Poly K) :
    PolynomialCoeffEq (bivariateSubstitute (rows.map (Poly.smul b)) curve)
      ((Poly.C b)*bivariateSubstitute rows curve) := by
  induction rows with
  | nil => intro i;change 0=(Poly.C b*Poly.zero).coeff i;rw [product_zero]
  | cons row rest ih =>
    intro i
    have through:=polynomial_mul_congr curve curve _ _ (fun _=>rfl) ih i
    change (Poly.smul b row+curve*bivariateSubstitute (rest.map (Poly.smul b)) curve).coeff i=_
    rw [Poly.coeff_add,Poly.coeff_smul,through,swap,constant_product,constant_product]
    simp only [bivariateSubstitute,Poly.coeff_add]
    grind

private theorem substitute_congr (rows : List (Poly K)) (f g : Poly K)
    (same : PolynomialCoeffEq f g) :
    PolynomialCoeffEq (bivariateSubstitute rows f) (bivariateSubstitute rows g) := by
  induction rows with
  | nil => intro i;rfl
  | cons row rest ih =>
    intro i
    simp only [bivariateSubstitute,Poly.coeff_add]
    rw [polynomial_mul_congr f g _ _ same ih i]

/-- Translating X commutes with substituting the correspondingly translated curve. -/
theorem polynomial_translate_substitution (rows : List (Poly K)) (curve : Poly K) (a : K) :
    PolynomialCoeffEq (polynomialTranslate (bivariateSubstitute rows curve) a)
      (bivariateSubstitute (rows.map (fun row=>polynomialTranslate row a)) (polynomialTranslate curve a)) := by
  induction rows with
  | nil => intro i;rfl
  | cons row rest ih =>
    intro i
    change (polynomialTranslate (row+curve*bivariateSubstitute rest curve) a).coeff i=_
    rw [translate_add,Poly.coeff_add,polynomial_translate_mul]
    have through:=polynomial_mul_congr (polynomialTranslate curve a) (polynomialTranslate curve a)
      _ _ (fun _=>rfl) ih i
    rw [through]
    simp only [List.map_cons,bivariateSubstitute,Poly.coeff_add]

/-- Formal Y-translation/substitution compatibility. -/
theorem bivariate_translate_y_substitution (rows : List (Poly K)) (b : K) (curve : Poly K) :
    PolynomialCoeffEq (bivariateSubstitute (bivariateTranslateY rows b) curve)
      (bivariateSubstitute rows (Poly.C b+curve)) := by
  induction rows with
  | nil => intro i;rfl
  | cons row rest ih =>
    intro i
    simp only [bivariateTranslateY]
    rw [substitute_add,Poly.coeff_add,substitute_add,Poly.coeff_add,substitute_scale]
    simp only [bivariateSubstitute,Poly.coeff_add,zero_coeff,product_zero]
    have p:=polynomial_mul_congr (Poly.C b) (Poly.C b) _ _ (fun _=>rfl) ih i
    have q:=polynomial_mul_congr curve curve _ _ (fun _=>rfl) ih i
    rw [p,q,polynomial_add_mul,Poly.coeff_add]
    grind

/-- Exact translation/substitution identity at the curve center, with no
finite-domain separation premise. -/
theorem bivariate_translation_substitution (rows : List (Poly K)) (curve : Poly K) (a : K) :
    PolynomialCoeffEq (polynomialTranslate (bivariateSubstitute rows curve) a)
      (bivariateSubstitute (bivariateTranslate rows a (curve.eval a)) (centeredCurve curve a)) := by
  intro i
  rw [polynomial_translate_substitution]
  unfold bivariateTranslate
  rw [bivariate_translate_y_substitution]
  apply substitute_congr _ _ _ ?_ i
  intro j
  rw [Poly.coeff_add,centeredCurve,Poly.coeff_sub]
  grind
end NearCompression
