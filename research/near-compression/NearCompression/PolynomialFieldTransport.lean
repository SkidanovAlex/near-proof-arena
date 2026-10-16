import NearCompression.IrreducibleDerivativeBezout

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K L : Type} [Field K] [Field L]

/-- Explicit unital coefficient homomorphism; the target may contain new roots. -/
structure PolynomialFieldMap (K L : Type) [Field K] [Field L] where
  toFun : K → L
  zero : toFun 0 = 0
  one : toFun 1 = 1
  add : ∀ x y, toFun (x+y) = toFun x + toFun y
  mul : ∀ x y, toFun (x*y) = toFun x * toFun y

def transportPolynomial (f : PolynomialFieldMap K L) (p : Poly K) : Poly L :=
  Poly.mk (p.coeffs.map f.toFun)

private theorem map_add_list (f : PolynomialFieldMap K L) (a b : List K) :
    (Poly.addL a b).map f.toFun = Poly.addL (a.map f.toFun) (b.map f.toFun) := by
  induction a generalizing b with
  | nil => rfl
  | cons c cs ih => cases b with
    | nil => rfl
    | cons d ds => simp only [Poly.addL,List.map_cons,f.add,ih]

private theorem map_mul_list (f : PolynomialFieldMap K L) (a b : List K) :
    (Poly.mulL a b).map f.toFun = Poly.mulL (a.map f.toFun) (b.map f.toFun) := by
  induction a with
  | nil => rfl
  | cons c cs ih =>
    simp only [Poly.mulL,map_add_list,Poly.scaleL,List.map_map,List.map_cons,f.zero,ih]
    congr 2
    funext x
    exact f.mul c x

theorem transport_polynomial_coefficient (f : PolynomialFieldMap K L) (p : Poly K) (i : Nat) :
    (transportPolynomial f p).coeff i = f.toFun (p.coeff i) := by
  cases p with | mk cs =>
    induction cs generalizing i with
    | nil => exact f.zero.symm
    | cons c cs ih => cases i with
      | zero => rfl
      | succ i => exact ih i

theorem transport_polynomial_add (f : PolynomialFieldMap K L) (p q : Poly K) :
    transportPolynomial f (p+q)=transportPolynomial f p+transportPolynomial f q := by
  exact congrArg Poly.mk (map_add_list f p.coeffs q.coeffs)

theorem transport_polynomial_mul (f : PolynomialFieldMap K L) (p q : Poly K) :
    transportPolynomial f (p*q)=transportPolynomial f p*transportPolynomial f q := by
  exact congrArg Poly.mk (map_mul_list f p.coeffs q.coeffs)

theorem transport_polynomial_derivative (f : PolynomialFieldMap K L) (p : Poly K) :
    transportPolynomial f (polynomialDerivative p)=polynomialDerivative (transportPolynomial f p) := by
  cases p with | mk cs =>
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      change transportPolynomial f (Poly.mk cs+Poly.X*polynomialDerivative (Poly.mk cs))=_
      rw [transport_polynomial_add,transport_polynomial_mul,ih]
      have hx : transportPolynomial f Poly.X=Poly.X := by
        simp [transportPolynomial,Poly.X,f.zero,f.one]
      rw [hx]
      rfl

/-- Unit Bezout certificates survive a change of coefficient field even if
irreducibility does not. -/
theorem transport_polynomial_bezout (f : PolynomialFieldMap K L) (p q A B : Poly K)
    (certificate : PolynomialCoeffEq (A*p+B*q) (Poly.C 1)) :
    PolynomialCoeffEq
      (transportPolynomial f A*transportPolynomial f p+
       transportPolynomial f B*transportPolynomial f q) (Poly.C 1) := by
  rw [←transport_polynomial_mul,←transport_polynomial_mul,←transport_polynomial_add]
  intro i
  rw [transport_polynomial_coefficient,certificate i]
  cases i <;> simp [Poly.C,Poly.coeff,List.getD,f.zero,f.one]

/-- Smoothness holds at new extension-field roots. No assumption that the
mapped polynomial remains irreducible is needed. Root existence is separate. -/
theorem irreducible_extension_root_smooth (f : PolynomialFieldMap K L)
    (characteristic : Nat) [IsCharP K characteristic] (p : Poly K) (d : Nat)
    (irreducible : PolynomialIrreducible p) (degree : p.DegLt (d+1))
    (leading : p.coeff d≠0) (positive : 0<d) (small : d<characteristic)
    (a : L) (root : (transportPolynomial f p).eval a=0) :
    (polynomialDerivative (transportPolynomial f p)).eval a≠0 := by
  obtain ⟨A,B,certificate⟩:=irreducible_derivative_bezout characteristic p d
    irreducible degree leading positive small
  have transported:=transport_polynomial_bezout f p (polynomialDerivative p) A B certificate
  rw [transport_polynomial_derivative] at transported
  exact bezout_no_common_root _ _ _ _ 1 a transported
    (fun zero=>Field.zero_ne_one zero.symm) root
end NearCompression
