import NearCompression.CodeSwitchFunctional
import ZkFormal.Algebra.Transport

/-! Pointwise fold identities for a closed verifier's structured functional.
These certify the algebraic update used by ext8_structured_functional.py,
not that program's implementation, transcript binding, or protocol soundness. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Every coefficient of a geometric functional folds to a geometric
functional with squared point and the updated mixer, including zero points. -/
theorem structured_power_fold (m z r : K) (i : Nat) :
    m*z^(2*i)+r*(m*z^(2*i+1)-m*z^(2*i)) =
      (m*(1-r+r*z))*(z*z)^i := by
  rw [Semiring.pow_succ, pow_two_mul]
  grind

/-- Low-bit tensor equality factor after one adjacent-coordinate fold. -/
theorem structured_tensor_fold (scale u rest r : K) :
    scale*(1-u)*rest+r*(scale*u*rest-scale*(1-u)*rest) =
      (scale*((1-r)*(1-u)+r*u))*rest := by
  grind

/-- Pointwise linearity composes the tensor component with injected powers. -/
theorem structured_sum_fold (a b c d r : K) :
    (a+c)+r*((b+d)-(a+c)) = (a+r*(b-a))+(c+r*(d-c)) := by
  grind

/-- The update agrees with the already-used affine-fold scale convention. -/
theorem structured_scale_eq (z r : K) : 1-r+r*z = oneFoldScale z r := by
  simp only [oneFoldScale]
  grind
end NearCompression
