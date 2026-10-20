import NearCompression.TerminalDAGEvaluation
import NearCompression.GKROutputWeights
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

structure TerminalLayerPlan where
  live : List Nat
  position : Nat → Nat
  gates : Nat → GKRWiringGate

/-- Each retained source node is either computed from the exact predecessor
slots or relayed by add(previousSlot,zeroSlot). This is structural, not an assumed
value equality. Zero padding slots use the same actual add-zero gate. -/
structure TerminalLayerRoute (nodes : Nat → TerminalDAGNode K) (sourceSize : Nat)
    (previousLive : List Nat) (previousPosition : Nat → Nat) (zeroSlot : Nat)
    (plan : TerminalLayerPlan) : Prop where
  liveBound : ∀ i∈plan.live,i<sourceSize
  zeroGate : plan.gates 0=⟨.add,zeroSlot,zeroSlot⟩
  routed : ∀ i∈plan.live,
    (∃ op left right,nodes i=.binary op left right ∧ left∈previousLive ∧ right∈previousLive ∧
      plan.gates (plan.position i)=⟨op,previousPosition left,previousPosition right⟩) ∨
    (i∈previousLive ∧ plan.gates (plan.position i)=⟨.add,previousPosition i,zeroSlot⟩)

theorem terminal_layer_route_values (inputs semantic previous : Nat → K)
    (nodes : Nat → TerminalDAGNode K) (sourceSize : Nat)
    (previousLive : List Nat) (previousPosition : Nat → Nat) (zeroSlot : Nat) (plan : TerminalLayerPlan)
    (route : TerminalLayerRoute nodes sourceSize previousLive previousPosition zeroSlot plan)
    (equations : ∀ i,i<sourceSize → semantic i=terminalNodeValue inputs semantic (nodes i))
    (old : ∀ i∈previousLive,previous (previousPosition i)=semantic i)
    (zeroValue : previous zeroSlot=0) :
    (∀ i∈plan.live,gkrLayerValues previous plan.gates (plan.position i)=semantic i) ∧
      gkrLayerValues previous plan.gates 0=0 := by
  constructor
  · intro i hi
    rcases route.routed i hi with ⟨op,left,right,node,hl,hr,gate⟩ | ⟨live,gate⟩
    · unfold gkrLayerValues
      rw [gate]
      dsimp only
      rw [old left hl,old right hr,equations i (route.liveBound i hi),node]
      rfl
    · unfold gkrLayerValues
      rw [gate]
      dsimp only [gkrGateValue]
      rw [old i live,zeroValue]
      grind
  · unfold gkrLayerValues
    rw [route.zeroGate]
    dsimp only [gkrGateValue]
    rw [zeroValue]
    grind

def terminalLayerRun (previous : Nat → K) : List TerminalLayerPlan → (Nat → K)
  | [] => previous
  | plan::rest => terminalLayerRun (gkrLayerValues previous plan.gates) rest

def terminalLastPlacement (live : List Nat) (position : Nat → Nat) :
    List TerminalLayerPlan → List Nat × (Nat → Nat)
  | [] => (live,position)
  | plan::rest => terminalLastPlacement plan.live plan.position rest

def TerminalRouteChain (nodes : Nat → TerminalDAGNode K) (sourceSize : Nat) :
    List Nat → (Nat → Nat) → Nat → List TerminalLayerPlan → Prop
  | _,_,_,[] => True
  | live,position,zeroSlot,plan::rest =>
      TerminalLayerRoute nodes sourceSize live position zeroSlot plan ∧
      TerminalRouteChain nodes sourceSize plan.live plan.position 0 rest

theorem terminal_layer_chain_values (inputs semantic previous : Nat → K)
    (nodes : Nat → TerminalDAGNode K) (sourceSize : Nat)
    (live : List Nat) (position : Nat → Nat) (zeroSlot : Nat) (plans : List TerminalLayerPlan)
    (chain : TerminalRouteChain nodes sourceSize live position zeroSlot plans)
    (equations : ∀ i,i<sourceSize → semantic i=terminalNodeValue inputs semantic (nodes i))
    (old : ∀ i∈live,previous (position i)=semantic i) (zeroValue : previous zeroSlot=0) :
    ∀ i∈(terminalLastPlacement live position plans).1,
      terminalLayerRun previous plans ((terminalLastPlacement live position plans).2 i)=semantic i := by
  induction plans generalizing live position zeroSlot previous with
  | nil => exact old
  | cons plan rest ih =>
    obtain ⟨next,nextZero⟩ := terminal_layer_route_values inputs semantic previous nodes sourceSize
      live position zeroSlot plan chain.1 equations old zeroValue
    exact ih (gkrLayerValues previous plan.gates) plan.live plan.position 0 chain.2 next nextZero

/-- Final theorem obtains node equations from the actual acyclic DAG evaluator.
No circuit-evaluation or AIR-satisfaction premise is supplied. Initial constant
and input placement is still an explicit interface, discharged separately. -/
theorem terminal_compiled_root (inputs : Nat → K) (nodes : List (TerminalDAGNode K))
    (acyclic : TerminalDAGAcyclic 0 nodes)
    (previous : Nat → K) (live : List Nat) (position : Nat → Nat) (zeroSlot : Nat)
    (plans : List TerminalLayerPlan)
    (chain : TerminalRouteChain (fun i => nodes.getD i (.constant 0)) nodes.length live position zeroSlot plans)
    (initial : ∀ i∈live,previous (position i)=terminalDAGRun inputs 0 (fun _ => 0) nodes i)
    (zeroValue : previous zeroSlot=0) (root : Nat)
    (rootLive : root∈(terminalLastPlacement live position plans).1) :
    terminalLayerRun previous plans ((terminalLastPlacement live position plans).2 root)=
      terminalDAGRun inputs 0 (fun _ => 0) nodes root := by
  apply terminal_layer_chain_values inputs (terminalDAGRun inputs 0 (fun _ => 0) nodes)
    previous (fun i => nodes.getD i (.constant 0)) nodes.length live position zeroSlot plans chain
    _ initial zeroValue root rootLive
  intro i hi
  have h := terminal_dag_node_equation inputs (fun _ => 0) nodes 0 acyclic i hi
  simpa only [Nat.zero_add,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using h
/-- Initial storage follows values(layout,private): private prefix, public
constant slots outside that prefix; unspecified constants are supplied as zero. -/
def terminalInitialValues (capacity : Nat) (inputs constants : Nat → K) (i : Nat) : K :=
  if i<capacity then inputs i else constants i

structure TerminalInitialRoute (nodes : Nat → TerminalDAGNode K) (sourceSize capacity : Nat)
    (constants : Nat → K) (live : List Nat) (position : Nat → Nat) (zeroSlot : Nat) : Prop where
  liveBound : ∀ i∈live,i<sourceSize
  zeroOutside : capacity≤zeroSlot
  zeroConstant : constants zeroSlot=0
  routed : ∀ i∈live,
    (∃ slot,nodes i=.input slot ∧ slot<capacity ∧ position i=slot) ∨
    (∃ value,nodes i=.constant value ∧ capacity≤position i ∧ constants (position i)=value)

theorem terminal_initial_route_values (inputs semantic constants : Nat → K)
    (nodes : Nat → TerminalDAGNode K) (sourceSize capacity : Nat)
    (live : List Nat) (position : Nat → Nat) (zeroSlot : Nat)
    (route : TerminalInitialRoute nodes sourceSize capacity constants live position zeroSlot)
    (equations : ∀ i,i<sourceSize → semantic i=terminalNodeValue inputs semantic (nodes i)) :
    (∀ i∈live,terminalInitialValues capacity inputs constants (position i)=semantic i) ∧
      terminalInitialValues capacity inputs constants zeroSlot=0 := by
  constructor
  · intro i hi
    rw [equations i (route.liveBound i hi)]
    rcases route.routed i hi with ⟨slot,node,bound,placed⟩ | ⟨value,node,outside,placed⟩
    · rw [node,placed]
      simp [terminalInitialValues,bound,terminalNodeValue]
    · rw [node]
      simp [terminalInitialValues,show ¬position i<capacity by omega,placed,terminalNodeValue]
  · simp [terminalInitialValues,show ¬zeroSlot<capacity by have h := route.zeroOutside; omega,
      route.zeroConstant]

/-- Combined certificate, with no assumed correct initial storage or assumed
correct circuit output. Producing these structural certificates for the Python
compiler (and linking its input program to AIR) remains explicit work. -/
theorem terminal_certified_root (inputs constants : Nat → K) (nodes : List (TerminalDAGNode K))
    (acyclic : TerminalDAGAcyclic 0 nodes) (capacity : Nat)
    (live : List Nat) (position : Nat → Nat) (zeroSlot : Nat) (plans : List TerminalLayerPlan)
    (initial : TerminalInitialRoute (fun i => nodes.getD i (.constant 0)) nodes.length capacity
      constants live position zeroSlot)
    (chain : TerminalRouteChain (fun i => nodes.getD i (.constant 0)) nodes.length live position zeroSlot plans)
    (root : Nat) (rootLive : root∈(terminalLastPlacement live position plans).1) :
    terminalLayerRun (terminalInitialValues capacity inputs constants) plans
      ((terminalLastPlacement live position plans).2 root)=
      terminalDAGRun inputs 0 (fun _ => 0) nodes root := by
  have equations : ∀ i,i<nodes.length → terminalDAGRun inputs 0 (fun _ => 0) nodes i=
      terminalNodeValue inputs (terminalDAGRun inputs 0 (fun _ => 0) nodes)
        (nodes.getD i (.constant 0)) := by
    intro i hi
    have h := terminal_dag_node_equation inputs (fun _ => 0) nodes 0 acyclic i hi
    simpa only [Nat.zero_add,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using h
  obtain ⟨placed,zeroValue⟩ := terminal_initial_route_values inputs _ constants _ nodes.length
    capacity live position zeroSlot initial equations
  exact terminal_compiled_root inputs nodes acyclic _ live position zeroSlot plans chain placed zeroValue root rootLive
end NearCompression
