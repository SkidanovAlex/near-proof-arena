import ZkFormal.Algebra.PolyLemmas

/-! Little-endian multilinear monomial tensors and the univariate coefficient
interpretation on the repeated-square curve. This is not Boolean-value MLE:
there are no `(1-x)` factors in monomial-coefficient evaluation. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

section Ring
variable {K : Type} [CommRing K]

def monomialEvenCoefficients : List K → List K
  | [] => []
  | [a] => [a]
  | a::_::rest => a::monomialEvenCoefficients rest

def monomialOddCoefficients : List K → List K
  | [] => []
  | [_] => []
  | _::b::rest => b::monomialOddCoefficients rest

def genericMonomialTensor : Nat → List K → (Nat → K) → K
  | 0,coefficients,_ => coefficients.getD 0 0
  | n+1,coefficients,point =>
      genericMonomialTensor n (monomialEvenCoefficients coefficients) (fun i => point (i+1)) +
      point 0*genericMonomialTensor n (monomialOddCoefficients coefficients) (fun i => point (i+1))

def genericMonomialCurve (x : K) : Nat → K
  | 0 => x
  | i+1 => genericMonomialCurve (x*x) i

/-- Pairwise splitting preserves all coefficients, with the even list longer
by at most one. This also covers odd-length zero-padded coefficient lists. -/
theorem monomial_split_lengths : ∀ coefficients : List K,
    (monomialEvenCoefficients coefficients).length+(monomialOddCoefficients coefficients).length=coefficients.length ∧
    (monomialOddCoefficients coefficients).length≤(monomialEvenCoefficients coefficients).length ∧
    (monomialEvenCoefficients coefficients).length≤(monomialOddCoefficients coefficients).length+1
  | [] => by simp [monomialEvenCoefficients,monomialOddCoefficients]
  | [a] => by simp [monomialEvenCoefficients,monomialOddCoefficients]
  | a::b::rest => by
    have ih := monomial_split_lengths rest
    simp only [monomialEvenCoefficients,monomialOddCoefficients,List.length_cons]
    omega

/-- Horner evaluation and the even/odd split are exactly equal in the ring. -/
theorem monomial_polynomial_split (x : K) : ∀ coefficients : List K,
    (Poly.mk coefficients).eval x=
      (Poly.mk (monomialEvenCoefficients coefficients)).eval (x*x)+
      x*(Poly.mk (monomialOddCoefficients coefficients)).eval (x*x)
  | [] => by simp only [monomialEvenCoefficients,monomialOddCoefficients,Poly.eval,Poly.evalL]; grind
  | [a] => by simp only [monomialEvenCoefficients,monomialOddCoefficients,Poly.eval,Poly.evalL]; grind
  | a::b::rest => by
    have ih := monomial_polynomial_split x rest
    simp only [monomialEvenCoefficients,monomialOddCoefficients,Poly.eval,Poly.evalL] at ih ⊢
    grind

/-- The recursive curve is precisely `[x,x²,x⁴,...]`. -/
theorem generic_monomial_curve_power (x : K) (i : Nat) : genericMonomialCurve x i=x^(2^i) := by
  induction i generalizing x with
  | zero => simp only [genericMonomialCurve,Nat.pow_zero,Semiring.pow_one]
  | succ i ih =>
    rw [genericMonomialCurve,ih,Nat.pow_succ,Nat.mul_comm (2^i) 2,pow_mul_eq]
    have square : x^2=x*x := by
      simp only [Semiring.pow_succ,Semiring.pow_zero]
      grind
    rw [square]

/-- Tensor evaluation on the curve equals univariate evaluation of the exact
same coefficients. Lists shorter than 2^n are implicitly padded with zero. -/
theorem generic_monomial_tensor_curve (n : Nat) (coefficients : List K)
    (size : coefficients.length≤2^n) (x : K) :
    genericMonomialTensor n coefficients (genericMonomialCurve x)=(Poly.mk coefficients).eval x := by
  induction n generalizing coefficients x with
  | zero =>
    cases coefficients with
    | nil => rfl
    | cons a rest =>
      have empty : rest=[] := by
        have len : rest.length=0 := by simp only [List.length_cons,Nat.pow_zero] at size; omega
        exact List.eq_nil_of_length_eq_zero len
      subst rest
      simp only [genericMonomialTensor,List.getD_cons_zero,Poly.eval,Poly.evalL]
      grind
  | succ n ih =>
    have lengths := monomial_split_lengths coefficients
    have even : (monomialEvenCoefficients coefficients).length≤2^n := by
      rw [Nat.pow_succ] at size
      omega
    have odd : (monomialOddCoefficients coefficients).length≤2^n := by omega
    change genericMonomialTensor n (monomialEvenCoefficients coefficients) (genericMonomialCurve (x*x)) +
      x*genericMonomialTensor n (monomialOddCoefficients coefficients) (genericMonomialCurve (x*x))=_
    rw [ih _ even,ih _ odd]
    exact (monomial_polynomial_split x coefficients).symm

theorem generic_monomial_tensor_power_curve (n : Nat) (coefficients : List K)
    (size : coefficients.length=2^n) (x : K) :
    genericMonomialTensor n coefficients (fun i => x^(2^i))=(Poly.mk coefficients).eval x := by
  have curve : (fun i => x^(2^i))=genericMonomialCurve x := by
    funext i
    exact (generic_monomial_curve_power x i).symm
  rw [curve]
  exact generic_monomial_tensor_curve n coefficients (Nat.le_of_eq size) x

end Ring
end NearCompression
