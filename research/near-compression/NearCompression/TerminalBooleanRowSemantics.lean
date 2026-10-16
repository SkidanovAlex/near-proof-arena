import NearCompression.WeightedTerminalSemantics
namespace NearCompression
open Lean.Grind ZkFormal.Air
variable {K : Type} [Field K]

/-- Only this row specialization identifies next with the cyclic successor and
selectors with row boundary indicators. Arbitrary terminal environments do not. -/
def terminalTraceEnvironment (trace : Trace K) (table row : Nat) : TerminalProgramEnvironment K where
  current := trace.cell table row
  next := trace.cell table ((row+1)%trace.height table)
  first := if row=0 then 1 else 0
  last := if row+1=trace.height table then 1 else 0
  transition := if row+1=trace.height table then 0 else 1

theorem terminal_boolean_row_source (trace : Trace K) (table row : Nat) (pubValues : List K) (e : Expr) :
    e.evalWith (airProgramEnv (terminalTraceEnvironment trace table row) pubValues)=
      e.eval trace table row pubValues := by
  change e.evalWith (airProgramEnv (terminalTraceEnvironment trace table row) pubValues)=
    e.evalWith (rowEnv trace table row pubValues)
  induction e with
  | const n => rfl
  | pub i => rfl
  | isFirst => rfl
  | isLast => rfl
  | isTransition => rfl
  | col c nx => cases nx <;> rfl
  | add a b ha hb =>
    change a.evalWith _+b.evalWith _=a.evalWith _+b.evalWith _
    rw [ha,hb]
  | mul a b ha hb =>
    change a.evalWith _*b.evalWith _=a.evalWith _*b.evalWith _
    rw [ha,hb]
  | neg a ha => exact congrArg Neg.neg ha

theorem terminal_boolean_row_residuals (trace : Trace K) (table row : Nat) (pubValues : List K)
    (source : List Expr) (auxiliary : List (BusProgramFormula K)) :
    terminalSourceAuxValues (terminalTraceEnvironment trace table row) pubValues source auxiliary=
      source.map (fun e => e.eval trace table row pubValues)++
        auxiliary.map (busProgramFormulaValue (terminalTraceEnvironment trace table row)) := by
  unfold terminalSourceAuxValues
  congr 1
  apply List.map_congr_left
  intro e he
  exact terminal_boolean_row_source trace table row pubValues e
end NearCompression
