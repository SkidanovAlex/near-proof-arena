import ZkFormal.Algebra.PolyLemmas

/-! Algebraic basis for omitting a sumcheck message's linear coefficient.
This proves exact coefficient recovery, not binary parsing or transcript code.
-/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem evalL_one_sum (xs : List K) : Poly.evalL 1 xs = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [Poly.evalL, List.sum_cons, ih]; grind

def recoverSumcheckLinear (claim c0 : K) (higher : List K) : K :=
  claim - c0 - c0 - higher.sum

theorem sumcheck_linear_recovery (claim c0 c1 : K) (higher : List K)
    (endpoint : (Poly.mk (c0::c1::higher)).eval 0 +
      (Poly.mk (c0::c1::higher)).eval 1 = claim) :
    recoverSumcheckLinear claim c0 higher = c1 := by
  simp only [Poly.eval, Poly.evalL, evalL_one_sum] at endpoint
  unfold recoverSumcheckLinear
  grind

theorem sumcheck_linear_endpoint (claim c0 : K) (higher : List K) :
    (Poly.mk (c0::recoverSumcheckLinear claim c0 higher::higher)).eval 0 +
      (Poly.mk (c0::recoverSumcheckLinear claim c0 higher::higher)).eval 1 = claim := by
  simp only [Poly.eval, Poly.evalL, evalL_one_sum, recoverSumcheckLinear]
  grind

theorem sumcheck_linear_roundtrip (claim c0 c1 : K) (higher : List K)
    (endpoint : (Poly.mk (c0::c1::higher)).eval 0 +
      (Poly.mk (c0::c1::higher)).eval 1 = claim) :
    c0::recoverSumcheckLinear claim c0 higher::higher = c0::c1::higher := by
  rw [sumcheck_linear_recovery claim c0 c1 higher endpoint]

end NearCompression
