import NearCompression.AIRProgramLowering
import NearCompression.TerminalProgramLayer

namespace NearCompression
open Lean.Grind ZkFormal.Air
variable {K : Type} [Field K]

/-- Full expression-to-physical-layer composition under structural certificates.
The expression environment may contain non-Boolean-point column values; this
statement does not identify them with trace rows or assert AIR satisfaction. -/
theorem air_layer_expression_value (env : TerminalProgramEnvironment K)
    (pubValues : List K) (e : Expr)
    (program : List (TerminalInstruction K)) (nodes : List (TerminalDAGNode K))
    (inputs constants : Nat → K)
    (sourceAcyclic : TerminalDAGAcyclic 0 (program.map (terminalProgramNode env)))
    (targetAcyclic : TerminalDAGAcyclic 0 nodes)
    (sourceRoot targetRoot capacity : Nat)
    (lowering : AIRProgramRoute (fun i => program.getD i terminalDefaultInstruction)
      pubValues e sourceRoot)
    (rebuild : TerminalRebuildRoute
      (fun i => (program.map (terminalProgramNode env)).getD i (.constant 0))
      (fun i => nodes.getD i (.constant 0)) inputs sourceRoot targetRoot)
    (live : List Nat) (position : Nat → Nat) (zeroSlot : Nat)
    (plans : List TerminalLayerPlan)
    (initial : TerminalInitialRoute (fun i => nodes.getD i (.constant 0)) nodes.length
      capacity constants live position zeroSlot)
    (chain : TerminalRouteChain (fun i => nodes.getD i (.constant 0)) nodes.length
      live position zeroSlot plans)
    (rootLive : targetRoot∈(terminalLastPlacement live position plans).1) :
    terminalLayerRun (terminalInitialValues capacity inputs constants) plans
      ((terminalLastPlacement live position plans).2 targetRoot)=
      e.evalWith (airProgramEnv env pubValues) := by
  rw [terminal_program_layer_value env program nodes inputs constants sourceAcyclic
    targetAcyclic sourceRoot targetRoot capacity rebuild live position zeroSlot plans
    initial chain rootLive]
  exact air_program_executed_value env pubValues program sourceAcyclic e sourceRoot lowering

end NearCompression
