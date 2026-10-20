import NearCompression.AIRProgramLowering
import NearCompression.TerminalCompiledCheck
namespace NearCompression
open Lean.Grind ZkFormal.Air

deriving instance DecidableEq for TerminalOpcode
deriving instance DecidableEq for TerminalInstruction

/-- Check the actual instruction operands, including zero padding, recursively
against the requested AIR AST. Public reads retain the source default-zero
semantics; column reads additionally require the caller's width bound. -/
def airExpressionCheck {K : Type} [Field K] [DecidableEq K]
    (program : List (TerminalInstruction K)) (pubValues : List K) (width : Nat) : Expr → Nat → Bool
  | expr,i =>
    let row := program.getD i terminalDefaultInstruction
    decide (i<program.length) &&
    match expr with
    | .const n => decide (row=⟨.constant,0,0,(@Nat.cast K Semiring.natCast n)⟩)
    | .pub p => decide (row=⟨.constant,0,0,pubValues.getD p 0⟩)
    | .col c nx => decide (c<width ∧ row=⟨(if nx then .next else .current),c,0,0⟩)
    | .isFirst => decide (row=⟨.first,0,0,0⟩)
    | .isLast => decide (row=⟨.last,0,0,0⟩)
    | .isTransition => decide (row=⟨.transition,0,0,0⟩)
    | .add a b => decide (row=⟨.add,row.left,row.right,0⟩) &&
        airExpressionCheck program pubValues width a row.left && airExpressionCheck program pubValues width b row.right
    | .mul a b => decide (row=⟨.mul,row.left,row.right,0⟩) &&
        airExpressionCheck program pubValues width a row.left && airExpressionCheck program pubValues width b row.right
    | .neg a => decide (row=⟨.sub,row.left,row.right,0⟩ ∧ row.left<program.length ∧
        program.getD row.left terminalDefaultInstruction=⟨.constant,0,0,0⟩) &&
        airExpressionCheck program pubValues width a row.right

theorem air_expression_checked {K : Type} [Field K] [DecidableEq K]
    (program : List (TerminalInstruction K)) (pubValues : List K) (width : Nat)
    (expr : Expr) (i : Nat) (h : airExpressionCheck program pubValues width expr i=true) :
    AIRProgramRoute (fun j => program.getD j terminalDefaultInstruction) pubValues expr i := by
  induction expr generalizing i with
  | const n =>
    simp only [airExpressionCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .constant h.2
  | pub p =>
    simp only [airExpressionCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .publicValue h.2
  | col c nx =>
    cases nx <;> simp only [airExpressionCheck,Bool.and_eq_true,decide_eq_true_eq,
      Bool.false_eq_true,ite_false,ite_true] at h
    · exact .current h.2.2
    · exact .next h.2.2
  | isFirst =>
    simp only [airExpressionCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .first h.2
  | isLast =>
    simp only [airExpressionCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .last h.2
  | isTransition =>
    simp only [airExpressionCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .transition h.2
  | add a b ha hb =>
    simp only [airExpressionCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .add (ha _ h.2.1.2) (hb _ h.2.2) h.2.1.1
  | mul a b ha hb =>
    simp only [airExpressionCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .mul (ha _ h.2.1.2) (hb _ h.2.2) h.2.1.1
  | neg a ha =>
    simp only [airExpressionCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .neg (ha _ h.2.2) h.2.1.2.2 h.2.1.1

theorem air_expression_checked_execution {K : Type} [Field K] [DecidableEq K]
    (env : TerminalProgramEnvironment K) (program : List (TerminalInstruction K))
    (pubValues : List K) (width : Nat) (expr : Expr) (i : Nat)
    (acyclic : terminalAcyclicCheck 0 (program.map (terminalProgramNode env))=true)
    (checked : airExpressionCheck program pubValues width expr i=true) :
    terminalProgramRun env 0 (fun _ => 0) program i=expr.evalWith (airProgramEnv env pubValues) :=
  air_program_executed_value env pubValues program (terminal_acyclic_checked _ 0 acyclic) expr i
    (air_expression_checked program pubValues width expr i checked)

/-- When a compiled table root is an AIR expression, its emitted DAG value is
that expression's evaluation. Weighted accumulation and auxiliary bus formulas
need their own checked routes; they are not inferred by this theorem. -/
theorem air_expression_checked_compiled_table {K : Type} [Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (inputs : Nat → K) (table : TerminalCompiledTable K)
    (pubValues : List K) (width : Nat) (expr : Expr)
    (acyclic : terminalAcyclicCheck 0 nodes=true)
    (tableCheck : terminalCompiledTableCheck nodes inputs table=true)
    (exprCheck : airExpressionCheck table.program pubValues width expr table.sourceRoot=true) :
    terminalDAGRun inputs 0 (fun _ => 0) nodes table.entry.root=
      expr.evalWith (airProgramEnv table.environment pubValues) := by
  rw [terminal_compiled_table_checked nodes inputs table acyclic tableCheck]
  have sourceCheck : terminalAcyclicCheck 0 (table.program.map (terminalProgramNode table.environment))=true := by
    simp only [terminalCompiledTableCheck,Bool.and_eq_true] at tableCheck
    exact tableCheck.1
  exact air_expression_checked_execution table.environment table.program pubValues width expr table.sourceRoot sourceCheck exprCheck

private def expressionSmokeProgram : List (TerminalInstruction Rat) :=
  [⟨.constant,0,0,0⟩,⟨.current,0,0,0⟩,⟨.next,1,0,0⟩,⟨.constant,0,0,7⟩,
   ⟨.add,1,2,0⟩,⟨.mul,4,3,0⟩,⟨.sub,0,5,0⟩,⟨.first,0,0,0⟩,
   ⟨.last,0,0,0⟩,⟨.transition,0,0,0⟩]
private def expressionSmokeExpr : Expr := .neg (.mul (.add (.col 0 false) (.col 1 true)) (.pub 0))

/-- Mixed current/next ASTs, public/default constants and selectors; malformed
registers, width, negation anchor, operand identity and padding reject. -/
theorem air_expression_check_regressions :
    airExpressionCheck expressionSmokeProgram [7] 2 expressionSmokeExpr 6=true ∧
    airExpressionCheck expressionSmokeProgram [7] 2 (.const 7) 3=true ∧
    airExpressionCheck expressionSmokeProgram [7] 2 (.pub 99) 0=true ∧
    airExpressionCheck expressionSmokeProgram [7] 2 .isFirst 7=true ∧
    airExpressionCheck expressionSmokeProgram [7] 2 .isLast 8=true ∧
    airExpressionCheck expressionSmokeProgram [7] 2 .isTransition 9=true ∧
    airExpressionCheck expressionSmokeProgram [8] 2 expressionSmokeExpr 6=false ∧
    airExpressionCheck expressionSmokeProgram [7] 1 expressionSmokeExpr 6=false ∧
    airExpressionCheck expressionSmokeProgram [7] 2 (.col 1 false) 2=false ∧
    airExpressionCheck expressionSmokeProgram [7] 2 (.const 0) 99=false ∧
    airExpressionCheck [⟨.constant,0,0,(1:Rat)⟩,⟨.sub,0,0,0⟩] [] 0 (.neg (.const 1)) 1=false ∧
    airExpressionCheck [⟨.current,0,1,(0:Rat)⟩] [] 1 (.col 0 false) 0=false := by decide +kernel

end NearCompression
