import NearCompression.InterleavedRSPullback
import NearCompression.ScalarRSTerminal
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def coefficientDot : List K → List K → K
  | [],_ => 0
  | w::ws,cs => w*cs.getD 0 0+coefficientDot ws (cs.drop 1)

theorem scalar_residual_dot (p : Poly K) (weights : List K) (offset : Nat) :
    scalarRSResidualFrom p offset weights=coefficientDot weights (p.coeffs.drop offset) := by
  induction weights generalizing offset with
  | nil => rfl
  | cons w ws ih =>
    simp only [scalarRSResidualFrom,coefficientDot,ih,List.drop_drop]
    have head : (p.coeffs.drop offset).getD 0 0=p.coeff offset := by
      simp [List.getD,List.getElem?_drop,Poly.coeff]
    rw [head]

theorem interleaved_coefficient_dot (weights even odd : List K) (w0 w1 : K) :
    coefficientDot (rsInterleave (weights.map (fun x => w0*x)) (weights.map (fun x => w1*x)))
      (rsInterleave even odd)=
      w0*coefficientDot weights even+w1*coefficientDot weights odd := by
  induction weights generalizing even odd with
  | nil => simp only [List.map_nil,rsInterleave,coefficientDot]; grind
  | cons w ws ih =>
    cases even with
    | nil => cases odd with
      | nil =>
        have h := ih [] []
        simp only [List.map_cons,rsInterleave,coefficientDot,List.getD_nil,List.drop_nil] at h ⊢
        grind
      | cons o os =>
        have h := ih [] os
        simp only [List.map_cons,rsInterleave,coefficientDot,List.getD_cons_zero,
          List.drop_succ_cons,List.drop_zero,List.getD_nil,List.drop_nil] at h ⊢
        grind
    | cons e es => cases odd with
      | nil =>
        have h := ih es []
        simp only [List.map_cons,rsInterleave,coefficientDot,List.getD_cons_zero,
          List.drop_succ_cons,List.drop_zero,List.getD_nil,List.drop_nil] at h ⊢
        grind
      | cons o os =>
        have h := ih es os
        simp only [List.map_cons,rsInterleave,coefficientDot,List.getD_cons_zero,
          List.drop_succ_cons,List.drop_zero] at h ⊢
        grind

/-- Actual coefficient residual on the constructed parent, with the two low
coordinate weights interleaved in the verifier's little-endian order. -/
theorem scalar_residual_interleaved (weights even odd : List K) (w0 w1 : K) :
    scalarRSResidual (rsInterleave (weights.map (fun x => w0*x)) (weights.map (fun x => w1*x)))
      (Poly.mk (rsInterleave even odd))=
    w0*scalarRSResidual weights (Poly.mk even)+w1*scalarRSResidual weights (Poly.mk odd) := by
  simp only [scalarRSResidual,scalar_residual_dot,List.drop_zero]
  exact interleaved_coefficient_dot weights even odd w0 w1
end NearCompression
