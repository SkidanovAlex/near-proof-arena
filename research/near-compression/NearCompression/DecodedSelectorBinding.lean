import NearCompression.DecodedFormulaCircuit
import NearCompression.AirSelectorProducts
import NearCompression.GenericPackedOpeningComposition
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

/-- Exact verifier selector products, including the zero-dimensional case. -/
def symbolicSelectorCheck {K : Type} [Field K] [DecidableEq K]
    (rowLog : Nat) (placement : TerminalSymbolicPlacement K) (point : List K) : Bool :=
  decide (point.length=rowLog ∧ placement.first=(point.map (fun x => 1-x)).prod ∧
    placement.last=point.prod ∧ placement.transition=1-point.prod)

/-- The intended row environment uses one point for every column and the
MLEs of the boundary flags. Next columns are cyclically shifted before MLE. -/
def decodedRowEnvironment {K : Type} [Field K] (rowLog : Nat)
    (decoded : Nat → Nat → K) (point : List K) : TerminalProgramEnvironment K :=
  ⟨(fun c => packedGridEval rowLog (decoded c) point),
   (fun c => packedGridEval rowLog (fun r => decoded c ((r+1)%2^rowLog)) point),
   packedGridEval rowLog (fun r => if r=0 then 1 else 0) point,
   packedGridEval rowLog (fun r => if r+1=2^rowLog then 1 else 0) point,
   packedGridEval rowLog (fun r => if r+1=2^rowLog then 0 else 1) point⟩

theorem symbolic_selector_checked {K : Type} [Field K] [DecidableEq K]
    (rowLog : Nat) (placement : TerminalSymbolicPlacement K) (point : List K)
    (checked : symbolicSelectorCheck rowLog placement point=true) :
    placement.first=packedGridEval rowLog (fun r => if r=0 then 1 else 0) point ∧
    placement.last=packedGridEval rowLog (fun r => if r+1=2^rowLog then 1 else 0) point ∧
    placement.transition=packedGridEval rowLog (fun r => if r+1=2^rowLog then 0 else 1) point := by
  simp only [symbolicSelectorCheck,decide_eq_true_eq] at checked
  rw [←checked.1,air_first_selector_product,air_last_selector_product,air_transition_selector_product]
  exact checked.2

/-- Only in-range lane coordinates must match the common table point. No
assumption is made about padded coordinates or unused columns. -/
theorem decoded_common_point_environment {K : Type} [Field K] [DecidableEq K]
    (table : GKRTableMetadata) (placement : TerminalSymbolicPlacement K)
    (decoded : Nat → Nat → K) (rowpoints : GKRSourceLane → Nat → K) (point : List K)
    (selectors : symbolicSelectorCheck table.rowLog placement point=true)
    (aligned : ∀ c,c<table.sourceWidth+table.auxiliaryWidth → ∀ i,i<table.rowLog →
      rowpoints (metadataColumnLane table c) i=point.getD i 0) :
    TerminalEnvironmentAgreement (table.sourceWidth+table.auxiliaryWidth)
      (decodedColumnEnvironment table placement decoded rowpoints)
      (decodedRowEnvironment table.rowLog decoded point) := by
  have hs := symbolic_selector_checked table.rowLog placement point selectors
  refine ⟨?_,?_,hs.1,hs.2.1,hs.2.2⟩
  · intro c hc
    exact packed_row_mle_point_congr table.rowLog (decoded c) _ _ (aligned c hc)
  · intro c hc
    exact packed_row_mle_point_congr table.rowLog (fun r => decoded c ((r+1)%2^table.rowLog)) _ _ (aligned c hc)

theorem decoded_common_point_mixture {K : Type} [Field K] [DecidableEq K]
    (table : GKRTableMetadata) (placement : TerminalSymbolicPlacement K)
    (decoded : Nat → Nat → K) (rowpoints : GKRSourceLane → Nat → K) (point : List K)
    (selectors : symbolicSelectorCheck table.rowLog placement point=true)
    (aligned : ∀ c,c<table.sourceWidth+table.auxiliaryWidth → ∀ i,i<table.rowLog →
      rowpoints (metadataColumnLane table c) i=point.getD i 0)
    (program : List (TerminalInstruction K)) (publicValues : List K) (width : Nat)
    (mixing power : K) (residuals : List (AIRBusResidual K × Nat))
    (widthBound : width≤table.sourceWidth+table.auxiliaryWidth)
    (checked : residuals.all (fun r => airBusResidualCheck program publicValues width r.1 r.2)=true) :
    airBusMixValue (decodedColumnEnvironment table placement decoded rowpoints) publicValues mixing power residuals=
    airBusMixValue (decodedRowEnvironment table.rowLog decoded point) publicValues mixing power residuals := by
  have full := decoded_common_point_environment table placement decoded rowpoints point selectors aligned
  have narrow : TerminalEnvironmentAgreement width _ _ :=
    ⟨(fun c hc => full.current c (by omega)),(fun c hc => full.next c (by omega)),
      full.first,full.last,full.transition⟩
  exact mixed_sum_environment_transport program publicValues width _ _ narrow mixing power residuals checked

/-- Off-Boolean selectors need not be Boolean. Empty products describe a
single row, where both boundary flags are one and transition is zero. -/
theorem decoded_selector_regressions :
    symbolicSelectorCheck 0 (⟨0,1,1,1,0⟩ : TerminalSymbolicPlacement Rat) []=true ∧
    symbolicSelectorCheck 2 (⟨0,1,2,6,-5⟩ : TerminalSymbolicPlacement Rat) [2,3]=true ∧
    symbolicSelectorCheck 2 (⟨0,1,2,6,1⟩ : TerminalSymbolicPlacement Rat) [2,3]=false ∧
    symbolicSelectorCheck 1 (⟨0,1,2,6,-5⟩ : TerminalSymbolicPlacement Rat) [2,3]=false ∧
    symbolicSelectorCheck 2 (⟨0,1,1,0,1⟩ : TerminalSymbolicPlacement Rat) [0,0]=true ∧
    symbolicSelectorCheck 2 (⟨0,1,0,1,0⟩ : TerminalSymbolicPlacement Rat) [1,1]=true := by decide +kernel

end NearCompression
