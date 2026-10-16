import NearCompression.TerminalDAGLayerCertificate
import NearCompression.GKRFixedInputEnvelope
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- Finite storage agrees with the routed wiring function at every stored gate. -/
theorem terminal_finite_gate_value (previous : Nat → K) (gates : List GKRWiringGate)
    (wiring : Nat → GKRWiringGate) (same : ∀ i,∀ hi : i<gates.length,wiring i=gates[i])
    (i : Nat) (bound : i<gates.length) :
    (gkrFiniteLayer previous gates).getD i 0=gkrLayerValues previous wiring i := by
  simp only [gkrFiniteLayer,List.getD,List.getElem?_map,List.getElem?_eq_getElem bound,
    Option.map_some,Option.getD_some,gkrLayerValues,same i bound]

/-- Existing DAG route certificates plus finite gate storage/placement bounds.
Out-of-range fallback values never substitute for live nodes or the zero gate. -/
def TerminalFiniteRouteChain (nodes : Nat → TerminalDAGNode K) (sourceSize : Nat) :
    List Nat → (Nat → Nat) → Nat → List (TerminalLayerPlan × List GKRWiringGate) → Prop
  | _,_,_,[] => True
  | live,position,zeroSlot,(plan,gates)::rest =>
      TerminalLayerRoute nodes sourceSize live position zeroSlot plan ∧
      0<gates.length ∧ (∀ i,∀ hi : i<gates.length,plan.gates i=gates[i]) ∧
      (∀ i∈plan.live,plan.position i<gates.length) ∧
      TerminalFiniteRouteChain nodes sourceSize plan.live plan.position 0 rest

/-- Connects the existing DAG route semantics to the exact finite evaluator
used by the recovered GKR circuit construction, including explicit padding. -/
theorem terminal_finite_chain_values (inputs semantic previous : Nat → K)
    (nodes : Nat → TerminalDAGNode K) (sourceSize : Nat)
    (live : List Nat) (position : Nat → Nat) (zeroSlot : Nat)
    (stages : List (TerminalLayerPlan × List GKRWiringGate))
    (chain : TerminalFiniteRouteChain nodes sourceSize live position zeroSlot stages)
    (equations : ∀ i,i<sourceSize → semantic i=terminalNodeValue inputs semantic (nodes i))
    (old : ∀ i∈live,previous (position i)=semantic i) (zeroValue : previous zeroSlot=0) :
    ∀ i∈(terminalLastPlacement live position (stages.map Prod.fst)).1,
      gkrFiniteCircuit previous (stages.map Prod.snd)
        ((terminalLastPlacement live position (stages.map Prod.fst)).2 i)=semantic i := by
  induction stages generalizing live position zeroSlot previous with
  | nil => exact old
  | cons stage rest ih =>
    obtain ⟨plan,gates⟩ := stage
    obtain ⟨route,positive,same,bounds,following⟩ := chain
    obtain ⟨next,nextZero⟩ := terminal_layer_route_values inputs semantic previous nodes sourceSize
      live position zeroSlot plan route equations old zeroValue
    apply ih (fun i => (gkrFiniteLayer previous gates).getD i 0) plan.live plan.position 0 following
    · intro i member
      rw [terminal_finite_gate_value previous gates plan.gates same (plan.position i) (bounds i member)]
      exact next i member
    · rw [terminal_finite_gate_value previous gates plan.gates same 0 positive]
      exact nextZero

/-- Acyclic DAG equations and certified initial placement discharge the
semantic premises for the finite layered root. -/
theorem terminal_finite_certified_root (inputs constants : Nat → K)
    (nodes : List (TerminalDAGNode K)) (acyclic : TerminalDAGAcyclic 0 nodes)
    (capacity : Nat) (live : List Nat) (position : Nat → Nat) (zeroSlot : Nat)
    (stages : List (TerminalLayerPlan × List GKRWiringGate))
    (initial : TerminalInitialRoute (fun i => nodes.getD i (.constant 0)) nodes.length
      capacity constants live position zeroSlot)
    (chain : TerminalFiniteRouteChain (fun i => nodes.getD i (.constant 0)) nodes.length
      live position zeroSlot stages)
    (root : Nat) (rootLive : root∈(terminalLastPlacement live position (stages.map Prod.fst)).1) :
    gkrFiniteCircuit (terminalInitialValues capacity inputs constants) (stages.map Prod.snd)
      ((terminalLastPlacement live position (stages.map Prod.fst)).2 root)=
      terminalDAGRun inputs 0 (fun _ => 0) nodes root := by
  have equations : ∀ i,i<nodes.length → terminalDAGRun inputs 0 (fun _ => 0) nodes i=
      terminalNodeValue inputs (terminalDAGRun inputs 0 (fun _ => 0) nodes)
        (nodes.getD i (.constant 0)) := by
    intro i hi
    have h := terminal_dag_node_equation inputs (fun _ => 0) nodes 0 acyclic i hi
    simpa only [Nat.zero_add,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using h
  obtain ⟨old,zero⟩ := terminal_initial_route_values inputs
    (terminalDAGRun inputs 0 (fun _ => 0) nodes) constants
    (fun i => nodes.getD i (.constant 0)) nodes.length capacity live position zeroSlot initial equations
  exact terminal_finite_chain_values inputs _ _ _ _ live position zeroSlot stages chain equations old zero root rootLive

end NearCompression
