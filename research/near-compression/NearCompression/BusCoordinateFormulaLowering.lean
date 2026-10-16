import NearCompression.BusResidualFailureWitness
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra

def busFormulaSum : List (BusProgramFormula Fp8) → BusProgramFormula Fp8
  | [] => .literal 0
  | x::xs => .add x (busFormulaSum xs)

def busCoordinateColumnFormula (width column : Nat) (next : Bool) : BusProgramFormula Fp8 :=
  let read := fun c=>if next then BusProgramFormula.next c else .current c
  if column<width then read column else
    busFormulaSum ((List.range 8).map (fun i=>
      .mul (.literal (ext8OperandBasis i)) (read (width+8*(column-width)+i))))

/-- Reconstruct extension auxiliaries inside the formula AST from eight
base coordinate columns; source columns retain their original indices. -/
def lowerBusCoordinates (width : Nat) : BusProgramFormula Fp8 → BusProgramFormula Fp8
  | .literal x => .literal x
  | .current c => busCoordinateColumnFormula width c false
  | .next c => busCoordinateColumnFormula width c true
  | .first => .first | .last => .last | .transition => .transition
  | .add a b => .add (lowerBusCoordinates width a) (lowerBusCoordinates width b)
  | .sub a b => .sub (lowerBusCoordinates width a) (lowerBusCoordinates width b)
  | .mul a b => .mul (lowerBusCoordinates width a) (lowerBusCoordinates width b)

def busCoordinateEnvironment (width : Nat) (env : TerminalProgramEnvironment Fp8) : TerminalProgramEnvironment Fp8 where
  current := fun c=>if c<width then env.current c else
    ((List.range 8).map (fun i=>ext8OperandBasis i*env.current (width+8*(c-width)+i))).sum
  next := fun c=>if c<width then env.next c else
    ((List.range 8).map (fun i=>ext8OperandBasis i*env.next (width+8*(c-width)+i))).sum
  first := env.first
  last := env.last
  transition := env.transition

theorem bus_formula_sum_value (env : TerminalProgramEnvironment Fp8) (xs : List (BusProgramFormula Fp8)) :
    busProgramFormulaValue env (busFormulaSum xs)=(xs.map (busProgramFormulaValue env)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [busFormulaSum,busProgramFormulaValue,List.map_cons,List.sum_cons,ih]

theorem bus_coordinate_formula_value (width : Nat) (env : TerminalProgramEnvironment Fp8)
    (e : BusProgramFormula Fp8) :
    busProgramFormulaValue env (lowerBusCoordinates width e)=
      busProgramFormulaValue (busCoordinateEnvironment width env) e := by
  induction e with
  | literal x | first | last | transition => rfl
  | current c | next c =>
    simp only [lowerBusCoordinates,busCoordinateColumnFormula,Bool.false_eq_true,ite_false,ite_true]
    split <;> rename_i hc <;> simp only [busProgramFormulaValue,busCoordinateEnvironment,hc,ite_true,ite_false,
      bus_formula_sum_value,List.map_map,Function.comp_def]
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    simp only [lowerBusCoordinates,busProgramFormulaValue,ha,hb]

theorem ext8_coordinate_sum (coordinates : Nat → Fp) :
    ((List.range 8).map (fun i=>ext8OperandBasis i*Fp8.ofBase (coordinates i))).sum=Fp8.ofCoeffs coordinates := by
  have h := ext8_operand_weighted (Fp8.ofCoeffs coordinates) 1
  have same : ((List.range 8).map (fun i=>(1*ext8OperandBasis i)*Fp8.ofBase (Fp8.coeff (Fp8.ofCoeffs coordinates) i)))=
      (List.range 8).map (fun i=>ext8OperandBasis i*Fp8.ofBase (coordinates i)) := by
    apply List.map_congr_left
    intro i hi
    rw [Fp8.coeff_ofCoeffs coordinates i (List.mem_range.mp hi)]
    grind
  rw [same] at h
  grind

/-- Exact Boolean-row semantics, including cyclic next rows and selectors. -/
theorem bus_coordinate_row_environment (raw : Trace Fp) (sourceWidth : Nat → Nat) (t row : Nat) :
    busCoordinateEnvironment (sourceWidth t) (busRowProgramEnv (airExt8Trace raw) t row)=
      busRowProgramEnv (airAuxCoordinateTrace raw sourceWidth) t row := by
  unfold busCoordinateEnvironment busRowProgramEnv rowEnv airExt8Trace airAuxCoordinateTrace
  simp only [Trace.height,ext8_coordinate_sum]
  rfl

theorem bus_coordinate_lowering_row_value (raw : Trace Fp) (sourceWidth : Nat → Nat)
    (t row : Nat) (e : BusProgramFormula Fp8) :
    busProgramFormulaValue (busRowProgramEnv (airExt8Trace raw) t row) (lowerBusCoordinates (sourceWidth t) e)=
      busProgramFormulaValue (busRowProgramEnv (airAuxCoordinateTrace raw sourceWidth) t row) e := by
  rw [bus_coordinate_formula_value,bus_coordinate_row_environment]

theorem bus_formula_sum_degree (xs : List (BusProgramFormula Fp8)) (d : Nat)
    (bounds : ∀ e∈xs,busFormulaDegree e≤d) : busFormulaDegree (busFormulaSum xs)≤d := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    apply Nat.max_le.mpr
    exact ⟨bounds x (by simp),ih (fun e he=>bounds e (by simp [he]))⟩

theorem bus_coordinate_column_degree (width column : Nat) (next : Bool) :
    busFormulaDegree (busCoordinateColumnFormula width column next)≤1 := by
  by_cases hc : column<width
  · cases next <;> simp [busCoordinateColumnFormula,hc,busFormulaDegree]
  · simp only [busCoordinateColumnFormula,hc,ite_false]
    apply bus_formula_sum_degree
    intro e he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
    cases next <;> simp [busFormulaDegree]

/-- Coordinate reconstruction is linear, so lowering does not increase the
local polynomial degree used by sumcheck soundness. -/
theorem bus_coordinate_lowering_degree (width : Nat) (e : BusProgramFormula Fp8) :
    busFormulaDegree (lowerBusCoordinates width e)≤busFormulaDegree e := by
  induction e with
  | literal x | first | last | transition => exact Nat.le_refl _
  | current c => exact bus_coordinate_column_degree width c false
  | next c => exact bus_coordinate_column_degree width c true
  | add a b ha hb | sub a b ha hb => exact Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _),Nat.le_trans hb (Nat.le_max_right _ _)⟩
  | mul a b ha hb => exact Nat.add_le_add ha hb

/-- Decoded PCS coordinates must themselves descend to the base field. This
explicit typing premise is stronger than source-column descent alone. -/
theorem decoded_bus_coordinate_lowering (tr : Trace Fp8) (sourceWidth : Nat → Nat)
    (base : ∀ t row column,Fp8.IsBase (tr.cell t row column))
    (t row : Nat) (e : BusProgramFormula Fp8) :
    busProgramFormulaValue (busRowProgramEnv tr t row) (lowerBusCoordinates (sourceWidth t) e)=
      busProgramFormulaValue (busRowProgramEnv (airAuxCoordinateTrace (decodedBaseTrace tr) sourceWidth) t row) e := by
  have same : airExt8Trace (decodedBaseTrace tr)=tr := by
    cases tr with
    | mk log cell =>
      change (⟨log,fun t row column=>Fp8.ofBase (cell t row column).c0⟩ : Trace Fp8)=⟨log,cell⟩
      congr 1
      funext t row column
      exact decoded_base_trace_cell ⟨log,cell⟩ t row column (base t row column)
  have h := bus_coordinate_lowering_row_value (decodedBaseTrace tr) sourceWidth t row e
  rw [same] at h
  exact h

end NearCompression
