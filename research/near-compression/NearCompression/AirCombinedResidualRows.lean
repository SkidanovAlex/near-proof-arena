import NearCompression.AirExtensionLift
import NearCompression.BusProgramFormulas

namespace NearCompression
open Lean.Grind ZkFormal.Air
variable {K : Type} [Field K]

noncomputable def busMLEProgramEnv (tr : Trace K) (t : Nat) (point : List K) : TerminalProgramEnvironment K where
  current:=fun c=>(airProductSelectorEnv tr t [] point).col c false
  next:=fun c=>(airProductSelectorEnv tr t [] point).col c true
  first:=(airProductSelectorEnv tr t [] point).isFirst
  last:=(airProductSelectorEnv tr t [] point).isLast
  transition:=(airProductSelectorEnv tr t [] point).isTransition

def busRowProgramEnv (tr : Trace K) (t r : Nat) : TerminalProgramEnvironment K where
  current:=fun c=>(rowEnv tr t r []).col c false
  next:=fun c=>(rowEnv tr t r []).col c true
  first:=(rowEnv tr t r []).isFirst
  last:=(rowEnv tr t r []).isLast
  transition:=(rowEnv tr t r []).isTransition

/-- Auxiliary gate formulas use the same Boolean rows and selectors as the
source AST, including extension constants, square chains and boundary gates. -/
theorem bus_formula_boolean_row (tr : Trace K) (t : Nat) (point : List K)
    (length : point.length=tr.log t) (boolean : ∀ x∈point,x=0 ∨ x=1) (formula : BusProgramFormula K) :
    busProgramFormulaValue (busMLEProgramEnv tr t point) formula=
      busProgramFormulaValue (busRowProgramEnv tr t (airBooleanIndex point)) formula := by
  induction formula with
  | literal value => rfl
  | current c => exact air_product_selector_expression_boolean tr t [] point length boolean (.col c false)
  | next c => exact air_product_selector_expression_boolean tr t [] point length boolean (.col c true)
  | first => exact air_product_selector_expression_boolean tr t [] point length boolean .isFirst
  | last => exact air_product_selector_expression_boolean tr t [] point length boolean .isLast
  | transition => exact air_product_selector_expression_boolean tr t [] point length boolean .isTransition
  | add a b ha hb => simp only [busProgramFormulaValue,ha,hb]
  | sub a b ha hb => simp only [busProgramFormulaValue,ha,hb]
  | mul a b ha hb => simp only [busProgramFormulaValue,ha,hb]

noncomputable def airCombinedRowResiduals (tr : Trace K) (t : Nat) (pub : List K)
    (source : List Expr) (auxiliary : List (BusProgramFormula K)) (r : Nat) : List K :=
  source.map (fun e=>e.eval tr t r pub) ++ auxiliary.map (busProgramFormulaValue (busRowProgramEnv tr t r))

noncomputable def airCombinedPointResiduals (tr : Trace K) (t : Nat) (pub : List K)
    (source : List Expr) (auxiliary : List (BusProgramFormula K)) (point : List K) : List K :=
  source.map (fun e=>e.evalWith (airProductSelectorEnv tr t pub point)) ++
    auxiliary.map (busProgramFormulaValue (busMLEProgramEnv tr t point))

/-- Source then auxiliary residual order is preserved exactly. -/
theorem air_combined_residual_boolean (tr : Trace K) (t : Nat) (pub : List K)
    (source : List Expr) (auxiliary : List (BusProgramFormula K)) (point : List K)
    (length : point.length=tr.log t) (boolean : ∀ x∈point,x=0 ∨ x=1) :
    airCombinedPointResiduals tr t pub source auxiliary point=
      airCombinedRowResiduals tr t pub source auxiliary (airBooleanIndex point) := by
  unfold airCombinedPointResiduals airCombinedRowResiduals
  congr 1
  · apply List.map_congr_left
    intro e _
    exact air_product_selector_expression_boolean tr t pub point length boolean e
  · apply List.map_congr_left
    intro formula _
    exact bus_formula_boolean_row tr t point length boolean formula

/-- Initial zero-count bound for the combined source and auxiliary formula
list. Constants/formulas and the common trace are fixed before batching. -/
theorem air_combined_weighted_zero_count (tr : Trace K) (t : Nat) (pub : List K)
    (source : List Expr) (auxiliary : List (BusProgramFormula K))
    (n row lane : Nat) (height : tr.log t=n+1) (positive : 0<source.length+auxiliary.length)
    (rowBound : row<2^(n+1))
    (wrong : (airCombinedRowResiduals tr t pub source auxiliary row).getD lane 0≠0)
    (sample : List K) (distinct : sample.Nodup) :
    ArenaCore.Security.count
      (sample.flatMap (fun mixing=>(packedGrid sample (n+1)).map (fun point=>(mixing,point))))
      (fun pair=>whirCubeSum (n+1) (fun bits=>whirKernel pair.2 bits*
        lanePowerBatch pair.1 (airCombinedPointResiduals tr t pub source auxiliary bits))=0) ≤
      (source.length+auxiliary.length-1)*sample.length^(n+1)+sample.length*((n+1)*sample.length^n) := by
  apply air_weighted_target_zero_count n (source.length+auxiliary.length) row lane
    (airCombinedRowResiduals tr t pub source auxiliary) positive rowBound
    (by simp [airCombinedRowResiduals]) wrong
    (fun mixing bits=>lanePowerBatch mixing (airCombinedPointResiduals tr t pub source auxiliary bits))
    ?_ sample distinct
  intro mixing bits length boolean
  rw [air_combined_residual_boolean tr t pub source auxiliary bits (length.trans height.symm) boolean]
  rw [←length,air_boolean_mle_value bits _ boolean]

end NearCompression
