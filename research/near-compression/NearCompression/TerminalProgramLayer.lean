import NearCompression.TerminalRebuildCertificate
import NearCompression.TerminalDAGLayerCertificate

namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- Composition of source reconstruction with physical layer routing. Input
bindings and both structural certificates remain explicit; neither output
agreement nor source validity is assumed. -/
theorem terminal_program_layer_value (env : TerminalProgramEnvironment K)
    (program : List (TerminalInstruction K)) (nodes : List (TerminalDAGNode K))
    (inputs constants : Nat → K)
    (sourceAcyclic : TerminalDAGAcyclic 0 (program.map (terminalProgramNode env)))
    (targetAcyclic : TerminalDAGAcyclic 0 nodes)
    (sourceRoot targetRoot capacity : Nat)
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
      terminalProgramRun env 0 (fun _ => 0) program sourceRoot := by
  rw [terminal_certified_root inputs constants nodes targetAcyclic capacity live position
    zeroSlot plans initial chain targetRoot rootLive]
  exact terminal_program_rebuilt_value env program nodes inputs sourceAcyclic
    targetAcyclic sourceRoot targetRoot rebuild

end NearCompression
