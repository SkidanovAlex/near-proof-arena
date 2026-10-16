import NearCompression.NativeStyleCoordinateAccumulation
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

deriving instance DecidableEq for BusProgramFormula

/-- Exact ordered specification built from the formal bus generator, then
lowered to the native-style Ext8 coordinate convention. -/
def generatedExt8BusSpec (interactions : List (BusFormulaInteraction Fp8))
    (sourceWidth : Nat) (finals : Nat → Fp8) : List (BusProgramFormula Fp8) :=
  (busTableResiduals interactions sourceWidth finals).map (lowerNativeStyleCoordinates sourceWidth)

def generatedExt8BusSpecCheck (interactions : List (BusFormulaInteraction Fp8))
    (sourceWidth : Nat) (finals : Nat → Fp8) (formulas : List (BusProgramFormula Fp8)) : Bool :=
  decide (formulas=generatedExt8BusSpec interactions sourceWidth finals)

/-- Passing exact specification checking binds all residuals, in order, to
the formal generator's values on the reconstructed environment. -/
theorem generated_ext8_bus_spec_checked (interactions : List (BusFormulaInteraction Fp8))
    (sourceWidth : Nat) (finals : Nat → Fp8) (formulas : List (BusProgramFormula Fp8))
    (checked : generatedExt8BusSpecCheck interactions sourceWidth finals formulas=true)
    (env : TerminalProgramEnvironment Fp8) :
    formulas.map (busProgramFormulaValue env)=
      (busTableResiduals interactions sourceWidth finals).map
        (busProgramFormulaValue (busCoordinateEnvironment sourceWidth env)) := by
  have same : formulas=generatedExt8BusSpec interactions sourceWidth finals := of_decide_eq_true checked
  rw [same]
  simp only [generatedExt8BusSpec,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  rw [native_style_lowering_value,bus_coordinate_formula_value]

end NearCompression
