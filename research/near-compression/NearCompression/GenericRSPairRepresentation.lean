import NearCompression.GenericMonomialTensor

/-! Scalar RS fiber pairs and even/odd coefficient coordinates. This module
proves only exact algebra, not proximity, commitment binding, or soundness. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

variable {K : Type} [Field K]

def rsPairEncode (x : K) (eo : K × K) : K × K :=
  (eo.1+x*eo.2, eo.1-x*eo.2)

def rsPairDecode (x : K) (ab : K × K) : K × K :=
  ((ab.1+ab.2)/2, (ab.1-ab.2)/(2*x))

theorem rs_pair_decode_encode (x : K) (h2 : (2 : K) ≠ 0) (hx : x ≠ 0)
    (eo : K × K) : rsPairDecode x (rsPairEncode x eo)=eo := by
  apply Prod.ext <;> simp only [rsPairDecode, rsPairEncode] <;> grind

theorem rs_pair_encode_decode (x : K) (h2 : (2 : K) ≠ 0) (hx : x ≠ 0)
    (ab : K × K) : rsPairEncode x (rsPairDecode x ab)=ab := by
  apply Prod.ext <;> simp only [rsPairDecode, rsPairEncode] <;> grind

theorem rs_polynomial_pair_encode (coefficients : List K) (x : K) :
    rsPairEncode x
      ((Poly.mk (monomialEvenCoefficients coefficients)).eval (x*x),
       (Poly.mk (monomialOddCoefficients coefficients)).eval (x*x)) =
      ((Poly.mk coefficients).eval x, (Poly.mk coefficients).eval (-x)) := by
  have hp := monomial_polynomial_split x coefficients
  have hm := monomial_polynomial_split (-x) coefficients
  have square : (-x)*(-x)=x*x := by grind
  rw [square] at hm
  apply Prod.ext <;> simp only [rsPairEncode] <;> grind

theorem rs_polynomial_pair_decode (coefficients : List K) (x : K)
    (h2 : (2 : K) ≠ 0) (hx : x ≠ 0) :
    rsPairDecode x ((Poly.mk coefficients).eval x, (Poly.mk coefficients).eval (-x)) =
      ((Poly.mk (monomialEvenCoefficients coefficients)).eval (x*x),
       (Poly.mk (monomialOddCoefficients coefficients)).eval (x*x)) := by
  rw [← rs_polynomial_pair_encode]
  exact rs_pair_decode_encode x h2 hx _

/-- The scalar evaluations in a leaf are the monomial tensor evaluated on
the two repeated-square curves. No Boolean-value interpolation is involved. -/
theorem rs_tensor_pair_decode (n : Nat) (coefficients : List K)
    (size : coefficients.length ≤ 2^n) (x : K)
    (h2 : (2 : K) ≠ 0) (hx : x ≠ 0) :
    rsPairDecode x
      (genericMonomialTensor n coefficients (genericMonomialCurve x),
       genericMonomialTensor n coefficients (genericMonomialCurve (-x))) =
      ((Poly.mk (monomialEvenCoefficients coefficients)).eval (x*x),
       (Poly.mk (monomialOddCoefficients coefficients)).eval (x*x)) := by
  rw [generic_monomial_tensor_curve n coefficients size x,
      generic_monomial_tensor_curve n coefficients size (-x)]
  exact rs_polynomial_pair_decode coefficients x h2 hx

/-- Arbitrary leaf pairs, including maliciously chosen ones, have unique
even/odd coordinates when the two fiber points are distinct. -/
theorem rs_pair_encode_injective (x : K) (h2 : (2 : K) ≠ 0) (hx : x ≠ 0)
    (a b : K × K) (h : rsPairEncode x a = rsPairEncode x b) : a=b := by
  have eq := congrArg (rsPairDecode x) h
  rw [rs_pair_decode_encode x h2 hx, rs_pair_decode_encode x h2 hx] at eq
  exact eq

/-- One folding challenge contracts the low monomial coordinate. The rest
of the coordinates lie on the repeated-square curve of x squared. -/
theorem rs_pair_fold_tensor (n : Nat) (coefficients : List K)
    (size : coefficients.length ≤ 2^(n+1)) (x r : K)
    (h2 : (2 : K) ≠ 0) (hx : x ≠ 0) :
    let eo := rsPairDecode x
      ((Poly.mk coefficients).eval x, (Poly.mk coefficients).eval (-x))
    eo.1+r*eo.2 = genericMonomialTensor (n+1) coefficients
      (fun i => match i with | 0 => r | j+1 => genericMonomialCurve (x*x) j) := by
  dsimp only
  rw [rs_polynomial_pair_decode coefficients x h2 hx]
  have lengths := monomial_split_lengths coefficients
  have even : (monomialEvenCoefficients coefficients).length ≤ 2^n := by
    rw [Nat.pow_succ] at size
    omega
  have odd : (monomialOddCoefficients coefficients).length ≤ 2^n := by omega
  simp only [genericMonomialTensor]
  rw [generic_monomial_tensor_curve n _ even, generic_monomial_tensor_curve n _ odd]

end NearCompression
