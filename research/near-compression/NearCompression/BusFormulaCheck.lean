import NearCompression.AIRAccumulatorCheck
import NearCompression.BusProgramFormulas
namespace NearCompression
open Lean.Grind ZkFormal.Air

/-- Bus formulas include extension-valued constants and binary subtraction.
Every leaf and operation is bound to the exact ABI instruction. -/
def busFormulaCheck {K : Type} [Field K] [DecidableEq K]
    (program : List (TerminalInstruction K)) (width : Nat) : BusProgramFormula K → Nat → Bool
  | formula,i =>
    let row := program.getD i terminalDefaultInstruction
    decide (i<program.length) &&
    match formula with
    | .literal value => decide (row=⟨.constant,0,0,value⟩)
    | .current c => decide (c<width ∧ row=⟨.current,c,0,0⟩)
    | .next c => decide (c<width ∧ row=⟨.next,c,0,0⟩)
    | .first => decide (row=⟨.first,0,0,0⟩)
    | .last => decide (row=⟨.last,0,0,0⟩)
    | .transition => decide (row=⟨.transition,0,0,0⟩)
    | .add a b => decide (row=⟨.add,row.left,row.right,0⟩) &&
        busFormulaCheck program width a row.left && busFormulaCheck program width b row.right
    | .sub a b => decide (row=⟨.sub,row.left,row.right,0⟩) &&
        busFormulaCheck program width a row.left && busFormulaCheck program width b row.right
    | .mul a b => decide (row=⟨.mul,row.left,row.right,0⟩) &&
        busFormulaCheck program width a row.left && busFormulaCheck program width b row.right

theorem bus_formula_checked {K : Type} [Field K] [DecidableEq K]
    (program : List (TerminalInstruction K)) (width : Nat) (formula : BusProgramFormula K) (i : Nat)
    (h : busFormulaCheck program width formula i=true) :
    BusProgramFormulaRoute (fun j => program.getD j terminalDefaultInstruction) formula i := by
  induction formula generalizing i with
  | literal value =>
    simp only [busFormulaCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .literal h.2
  | current c =>
    simp only [busFormulaCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .current h.2.2
  | next c =>
    simp only [busFormulaCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .next h.2.2
  | first =>
    simp only [busFormulaCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .first h.2
  | last =>
    simp only [busFormulaCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .last h.2
  | transition =>
    simp only [busFormulaCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .transition h.2
  | add a b ha hb =>
    simp only [busFormulaCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .add (ha _ h.2.1.2) (hb _ h.2.2) h.2.1.1
  | sub a b ha hb =>
    simp only [busFormulaCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .sub (ha _ h.2.1.2) (hb _ h.2.2) h.2.1.1
  | mul a b ha hb =>
    simp only [busFormulaCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .mul (ha _ h.2.1.2) (hb _ h.2.2) h.2.1.1

theorem bus_formula_checked_execution {K : Type} [Field K] [DecidableEq K]
    (env : TerminalProgramEnvironment K) (program : List (TerminalInstruction K))
    (width : Nat) (formula : BusProgramFormula K) (i : Nat)
    (acyclic : terminalAcyclicCheck 0 (program.map (terminalProgramNode env))=true)
    (checked : busFormulaCheck program width formula i=true) :
    terminalProgramRun env 0 (fun _ => 0) program i=busProgramFormulaValue env formula :=
  bus_program_formula_executed env program (terminal_acyclic_checked _ 0 acyclic) formula i
    (bus_formula_checked program width formula i checked)

abbrev AIRBusResidual (K : Type) := Sum Expr (BusProgramFormula K)

def airBusResidualValue {K : Type} [Field K] (env : TerminalProgramEnvironment K)
    (pubValues : List K) : AIRBusResidual K → K
  | .inl expr => expr.evalWith (airProgramEnv env pubValues)
  | .inr formula => busProgramFormulaValue env formula

def airBusResidualCheck {K : Type} [Field K] [DecidableEq K]
    (program : List (TerminalInstruction K)) (pubValues : List K) (width : Nat) : AIRBusResidual K → Nat → Bool
  | .inl expr,i => airExpressionCheck program pubValues width expr i
  | .inr formula,i => busFormulaCheck program width formula i

theorem air_bus_residual_checked {K : Type} [Field K] [DecidableEq K]
    (env : TerminalProgramEnvironment K) (program : List (TerminalInstruction K))
    (pubValues : List K) (width : Nat) (residual : AIRBusResidual K) (i : Nat)
    (acyclic : terminalAcyclicCheck 0 (program.map (terminalProgramNode env))=true)
    (checked : airBusResidualCheck program pubValues width residual i=true) :
    terminalProgramRun env 0 (fun _ => 0) program i=airBusResidualValue env pubValues residual := by
  cases residual with
  | inl expr => exact air_expression_checked_execution env program pubValues width expr i acyclic checked
  | inr formula => exact bus_formula_checked_execution env program width formula i acyclic checked

def airBusMixValue {K : Type} [Field K] (env : TerminalProgramEnvironment K)
    (pubValues : List K) (mixing : K) : K → List (AIRBusResidual K × Nat) → K
  | _,[] => 0
  | power,(formula,_)::rest => power*airBusResidualValue env pubValues formula+
      airBusMixValue env pubValues mixing (power*mixing) rest

theorem air_bus_mix_checked {K : Type} [Field K] [DecidableEq K]
    (env : TerminalProgramEnvironment K) (program : List (TerminalInstruction K))
    (pubValues : List K) (width : Nat) (mixing power : K) (residuals : List (AIRBusResidual K × Nat))
    (acyclic : terminalAcyclicCheck 0 (program.map (terminalProgramNode env))=true)
    (checked : residuals.all (fun r => airBusResidualCheck program pubValues width r.1 r.2)=true) :
    airMixValue (terminalProgramRun env 0 (fun _ => 0) program) mixing power (residuals.map Prod.snd)=
      airBusMixValue env pubValues mixing power residuals := by
  induction residuals generalizing power with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.all_cons,Bool.and_eq_true] at checked
    simp only [List.map_cons,airMixValue,airBusMixValue]
    rw [air_bus_residual_checked env program pubValues width r.1 r.2 acyclic checked.1,
      ih (power*mixing) checked.2]

/-- One ordered list may contain source AIR expressions and auxiliary bus
formulas. Identifying that list with the expected bus specification remains a
separate obligation; arbitrary supplied formulas do not imply bus validity. -/
theorem air_bus_weighted_compiled {K : Type} [Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (inputs : Nat → K) (table : TerminalCompiledTable K)
    (pubValues : List K) (width : Nat) (mixing : K) (residuals : List (AIRBusResidual K × Nat))
    (zeroReg total : Nat) (steps : List AIRAccumulatorStep)
    (acyclic : terminalAcyclicCheck 0 nodes=true)
    (tableCheck : terminalCompiledTableCheck nodes inputs table=true)
    (formulas : residuals.all (fun r => airBusResidualCheck table.program pubValues width r.1 r.2)=true)
    (accumulation : airWeightedProgramCheck table.program mixing (residuals.map Prod.snd)
      zeroReg total table.sourceRoot steps=true) :
    terminalDAGRun inputs 0 (fun _ => 0) nodes table.entry.root=
      airBusMixValue table.environment pubValues mixing 1 residuals := by
  rw [terminal_compiled_table_checked nodes inputs table acyclic tableCheck]
  simp only [terminalCompiledTableCheck,Bool.and_eq_true] at tableCheck
  rw [air_weighted_program_checked table.environment table.program mixing _ zeroReg total table.sourceRoot steps tableCheck.1 accumulation]
  exact air_bus_mix_checked table.environment table.program pubValues width mixing 1 residuals tableCheck.1 formulas

private def busSmokeProgram : List (TerminalInstruction Rat) :=
  [⟨.constant,0,0,-3⟩,⟨.current,0,0,0⟩,⟨.next,1,0,0⟩,⟨.sub,1,2,0⟩,
   ⟨.mul,0,3,0⟩,⟨.first,0,0,0⟩,⟨.last,0,0,0⟩,⟨.transition,0,0,0⟩,⟨.add,1,2,0⟩]
private def busSmokeFormula : BusProgramFormula Rat := .mul (.literal (-3)) (.sub (.current 0) (.next 1))

theorem bus_formula_check_regressions :
    busFormulaCheck busSmokeProgram 2 busSmokeFormula 4=true ∧
    busFormulaCheck busSmokeProgram 2 .first 5=true ∧
    busFormulaCheck busSmokeProgram 2 .last 6=true ∧
    busFormulaCheck busSmokeProgram 2 .transition 7=true ∧
    busFormulaCheck busSmokeProgram 2 (.add (.current 0) (.next 1)) 8=true ∧
    busFormulaCheck busSmokeProgram 2 (.literal 3) 0=false ∧
    busFormulaCheck busSmokeProgram 2 (.sub (.next 1) (.current 0)) 3=false ∧
    busFormulaCheck busSmokeProgram 1 busSmokeFormula 4=false ∧
    busFormulaCheck busSmokeProgram 2 (.current 1) 2=false ∧
    busFormulaCheck busSmokeProgram 2 (.literal 0) 99=false ∧
    busFormulaCheck [⟨.next,0,1,(0:Rat)⟩] 1 (.next 0) 0=false ∧
    ([(Sum.inl (.col 0 false),1),(Sum.inr busSmokeFormula,4)] : List (AIRBusResidual Rat × Nat)).all
      (fun r => airBusResidualCheck busSmokeProgram [] 2 r.1 r.2)=true := by decide +kernel

end NearCompression
