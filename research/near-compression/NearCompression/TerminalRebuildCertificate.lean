import NearCompression.TerminalDAGBalance
import NearCompression.TerminalProgramSemantics
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- Structural provenance of the rebuilt root. The input constructor explicitly
binds a source current/next value to the target private slot; it does not infer
that binding from source proximity. Expanded registers need no emitted node. -/
inductive TerminalRebuildRoute (source target : Nat → TerminalDAGNode K) (inputs : Nat → K) : Nat → Nat → Prop where
  | constant {i z value} : source i=.constant value → target z=.constant value → TerminalRebuildRoute source target inputs i z
  | input {i z slot} : source i=.constant (inputs slot) → target z=.input slot → TerminalRebuildRoute source target inputs i z
  | binary {i left right x y z op} : source i=.binary op left right →
      TerminalRebuildRoute source target inputs left x → TerminalRebuildRoute source target inputs right y →
      TerminalArithmeticRoute target op x y z → TerminalRebuildRoute source target inputs i z
  | expanded {i z} {terms : List (Nat × Bool)} {mapping : Nat → Nat} : TerminalSignedExpansion source i true terms →
      (∀ t∈terms,TerminalRebuildRoute source target inputs t.1 (mapping t.1)) →
      TerminalBalanceRoute target (terms.map (fun t => (mapping t.1,t.2))) z →
      TerminalRebuildRoute source target inputs i z

theorem terminal_rebuild_route_value (source target : Nat → TerminalDAGNode K)
    (sourceInputs sourceValues targetInputs targetValues : Nat → K)
    (sourceEquations : ∀ i,sourceValues i=terminalNodeValue sourceInputs sourceValues (source i))
    (targetEquations : ∀ i,targetValues i=terminalNodeValue targetInputs targetValues (target i))
    (i z : Nat) (route : TerminalRebuildRoute source target targetInputs i z) :
    targetValues z=sourceValues i := by
  induction route with
  | @constant i z value hs ht =>
    have a := sourceEquations i
    have b := targetEquations z
    simp only [hs,ht,terminalNodeValue] at a b
    exact b.trans a.symm
  | @input i z slot hs ht =>
    have a := sourceEquations i
    have b := targetEquations z
    simp only [hs,ht,terminalNodeValue] at a b
    exact b.trans a.symm
  | @binary i left right x y z op hs rl rr arithmetic hl hr =>
    have a := sourceEquations i
    rw [hs] at a
    have b := terminal_arithmetic_route_value target targetInputs targetValues targetEquations op x y z arithmetic
    rw [hl,hr] at b
    exact b.trans a.symm
  | @expanded i z terms mapping expansion routes balance ih =>
    exact terminal_rebuilt_expansion_value sourceInputs sourceValues targetInputs targetValues source target
      sourceEquations targetEquations i z terms mapping expansion ih balance

/-- Complete source-program-to-emitted-DAG value preservation from opcode
execution and structural rebuilding certificates. Both executions are defined;
there is no assumed compiler correctness, residual equality, or AIR validity. -/
theorem terminal_program_rebuilt_value (env : TerminalProgramEnvironment K)
    (program : List (TerminalInstruction K)) (target : List (TerminalDAGNode K))
    (inputs : Nat → K)
    (sourceAcyclic : TerminalDAGAcyclic 0 (program.map (terminalProgramNode env)))
    (targetAcyclic : TerminalDAGAcyclic 0 target)
    (root z : Nat)
    (route : TerminalRebuildRoute
      (fun i => (program.map (terminalProgramNode env)).getD i (.constant 0))
      (fun i => target.getD i (.constant 0)) inputs root z) :
    terminalDAGRun inputs 0 (fun _ => 0) target z=
      terminalProgramRun env 0 (fun _ => 0) program root := by
  rw [terminal_program_run_lower]
  exact terminal_rebuild_route_value _ _ (fun _ => 0) _ inputs _
    (terminal_dag_total_equations (fun _ => 0) _ sourceAcyclic)
    (terminal_dag_total_equations inputs target targetAcyclic) root z route
end NearCompression
