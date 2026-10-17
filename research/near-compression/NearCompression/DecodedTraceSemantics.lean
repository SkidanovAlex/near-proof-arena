import NearCompression.HistoryDecodedEnvironment
import NearCompression.AirCombinedResidualRows
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra

/-- A decoded column table supplies an actual AIR trace table. The trace API
is total; all table indices here denote the same selected table. No validity
of its rows is built into this construction. -/
def decodedTableTrace {K : Type} (rowLog : Nat) (decoded : Nat → Nat → K) : Trace K :=
  ⟨fun _ => rowLog,fun _ row column => decoded column row⟩

theorem decoded_air_row_environment {K : Type} [Field K]
    (rowLog : Nat) (decoded : Nat → Nat → K) (publicValues point : List K) :
    airProgramEnv (decodedRowEnvironment rowLog decoded point) publicValues=
      airRowMLEEnv (decodedTableTrace rowLog decoded) 0 publicValues point := by
  unfold airProgramEnv decodedRowEnvironment airRowMLEEnv decodedTableTrace Trace.height
  congr 1
  funext c next
  cases next <;> rfl

theorem decoded_bus_row_environment {K : Type} [Field K]
    (rowLog : Nat) (decoded : Nat → Nat → K) (point : List K) (length : point.length=rowLog) :
    decodedRowEnvironment rowLog decoded point=busMLEProgramEnv (decodedTableTrace rowLog decoded) 0 point := by
  unfold busMLEProgramEnv
  rw [air_product_selector_env _ _ _ _ length]
  rfl

/-- Register labels do not affect values. The weighted compiler accumulator
is the same ordered power batch used by the AIR soundness analysis. -/
theorem mixed_formula_power_batch {K : Type} [Field K]
    (env : TerminalProgramEnvironment K) (publicValues : List K) (mixing power : K)
    (residuals : List (AIRBusResidual K × Nat)) :
    airBusMixValue env publicValues mixing power residuals=
      power*lanePowerBatch mixing (residuals.map (fun r => airBusResidualValue env publicValues r.1)) := by
  induction residuals generalizing power with
  | nil => simp only [airBusMixValue,List.map_nil,lanePowerBatch];grind
  | cons r rest ih =>
    rcases r with ⟨formula,register⟩
    simp only [airBusMixValue,List.map_cons,lanePowerBatch,ih]
    grind

theorem decoded_combined_residual_values {K : Type} [Field K]
    (rowLog : Nat) (decoded : Nat → Nat → K) (publicValues point : List K)
    (length : point.length=rowLog) (source : List Expr) (auxiliary : List (BusProgramFormula K))
    (residuals : List (AIRBusResidual K × Nat))
    (order : residuals.map Prod.fst=source.map Sum.inl++auxiliary.map Sum.inr) :
    residuals.map (fun r => airBusResidualValue (decodedRowEnvironment rowLog decoded point) publicValues r.1)=
      airCombinedPointResiduals (decodedTableTrace rowLog decoded) 0 publicValues source auxiliary point := by
  have maps : residuals.map (fun r => airBusResidualValue (decodedRowEnvironment rowLog decoded point) publicValues r.1)=
      (residuals.map Prod.fst).map (airBusResidualValue (decodedRowEnvironment rowLog decoded point) publicValues) := by
    rw [List.map_map];rfl
  rw [maps,order,List.map_append,List.map_map,List.map_map]
  unfold airCombinedPointResiduals
  congr 1
  · apply List.map_congr_left
    intro expr _
    change expr.evalWith (airProgramEnv _ _)=_
    rw [decoded_air_row_environment,air_product_selector_env _ _ _ _ length]
  · apply List.map_congr_left
    intro formula _
    change busProgramFormulaValue _ formula=_
    rw [decoded_bus_row_environment rowLog decoded point length]

theorem decoded_combined_mixture {K : Type} [Field K]
    (rowLog : Nat) (decoded : Nat → Nat → K) (publicValues point : List K)
    (length : point.length=rowLog) (source : List Expr) (auxiliary : List (BusProgramFormula K))
    (residuals : List (AIRBusResidual K × Nat))
    (order : residuals.map Prod.fst=source.map Sum.inl++auxiliary.map Sum.inr) (mixing : K) :
    airBusMixValue (decodedRowEnvironment rowLog decoded point) publicValues mixing 1 residuals=
      lanePowerBatch mixing (airCombinedPointResiduals (decodedTableTrace rowLog decoded) 0 publicValues source auxiliary point) := by
  rw [mixed_formula_power_batch,decoded_combined_residual_values rowLog decoded publicValues point length source auxiliary residuals order]
  grind

/-- At Boolean points, the circuit-side mixture is exactly the ordered batch
of actual trace-row constraints, including auxiliary formulas. -/
theorem decoded_combined_mixture_boolean {K : Type} [Field K]
    (rowLog : Nat) (decoded : Nat → Nat → K) (publicValues point : List K)
    (length : point.length=rowLog) (boolean : ∀ x∈point,x=0 ∨ x=1)
    (source : List Expr) (auxiliary : List (BusProgramFormula K))
    (residuals : List (AIRBusResidual K × Nat))
    (order : residuals.map Prod.fst=source.map Sum.inl++auxiliary.map Sum.inr) (mixing : K) :
    airBusMixValue (decodedRowEnvironment rowLog decoded point) publicValues mixing 1 residuals=
      lanePowerBatch mixing (airCombinedRowResiduals (decodedTableTrace rowLog decoded) 0 publicValues source auxiliary (airBooleanIndex point)) := by
  rw [decoded_combined_mixture rowLog decoded publicValues point length source auxiliary residuals order,
    air_combined_residual_boolean _ _ _ _ _ _ length boolean]

/-- Existing initial zerocheck bound now applies to the compiler accumulator
on decoded columns. Formula/specification identity remains the explicit order
premise; this is an ideal finite-sample bound, not Fiat-Shamir security. -/
theorem decoded_mixture_weighted_zero_count {K : Type} [Field K]
    (n row lane : Nat) (decoded : Nat → Nat → K) (publicValues : List K)
    (source : List Expr) (auxiliary : List (BusProgramFormula K))
    (residuals : List (AIRBusResidual K × Nat))
    (order : residuals.map Prod.fst=source.map Sum.inl++auxiliary.map Sum.inr)
    (positive : 0<source.length+auxiliary.length) (rowBound : row<2^(n+1))
    (wrong : (airCombinedRowResiduals (decodedTableTrace (n+1) decoded) 0 publicValues source auxiliary row).getD lane 0≠0)
    (sample : List K) (distinct : sample.Nodup) :
    ArenaCore.Security.count
      (sample.flatMap (fun mixing => (packedGrid sample (n+1)).map (fun point => (mixing,point))))
      (fun pair => whirCubeSum (n+1) (fun bits => whirKernel pair.2 bits*
        airBusMixValue (decodedRowEnvironment (n+1) decoded bits) publicValues pair.1 1 residuals)=0) ≤
      (source.length+auxiliary.length-1)*sample.length^(n+1)+sample.length*((n+1)*sample.length^n) := by
  apply air_weighted_target_zero_count n (source.length+auxiliary.length) row lane
    (airCombinedRowResiduals (decodedTableTrace (n+1) decoded) 0 publicValues source auxiliary)
    positive rowBound (by simp [airCombinedRowResiduals]) wrong
    (fun mixing bits => airBusMixValue (decodedRowEnvironment (n+1) decoded bits) publicValues mixing 1 residuals)
    ?_ sample distinct
  intro mixing bits length boolean
  rw [decoded_combined_mixture_boolean (n+1) decoded publicValues bits length boolean source auxiliary residuals order]
  rw [←length,air_boolean_mle_value bits _ boolean]

end NearCompression
