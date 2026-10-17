import NearCompression.TerminalFiniteLayerCertificate
namespace NearCompression

deriving instance DecidableEq for GKRBinaryOp
deriving instance DecidableEq for GKRWiringGate

structure TerminalStoredPlan where
  live : List Nat
  positions : List Nat
  gates : List GKRWiringGate

def TerminalStoredPlan.plan (stored : TerminalStoredPlan) : TerminalLayerPlan :=
  ⟨stored.live,(fun i => stored.positions.getD i 0),
    (fun i => stored.gates.getD i ⟨.add,0,0⟩)⟩

def terminalStoredNodeCheck {K : Type} (nodes : List (TerminalDAGNode K))
    (previousLive : List Nat) (previousPosition : Nat → Nat) (zeroSlot : Nat)
    (stored : TerminalStoredPlan) (i : Nat) : Bool :=
  let actual := stored.plan.gates (stored.plan.position i)
  let relay := decide (i∈previousLive ∧ actual=⟨.add,previousPosition i,zeroSlot⟩)
  match nodes.getD i (.input 0) with
  | .binary op left right =>
      decide (left∈previousLive ∧ right∈previousLive ∧
        actual=⟨op,previousPosition left,previousPosition right⟩) || relay
  | _ => relay

def terminalStoredRouteCheck {K : Type} (nodes : List (TerminalDAGNode K))
    (previousLive : List Nat) (previousPosition : Nat → Nat) (zeroSlot : Nat)
    (stored : TerminalStoredPlan) : Bool :=
  decide (0<stored.gates.length) &&
  decide (stored.plan.gates 0=⟨.add,zeroSlot,zeroSlot⟩) &&
  stored.live.all (fun i => decide (i<nodes.length ∧ i<stored.positions.length ∧
    stored.plan.position i<stored.gates.length) &&
    terminalStoredNodeCheck nodes previousLive previousPosition zeroSlot stored i)

/-- A finite executable check supplies the structural route and storage bounds
required by the finite root-preservation theorem. No value evaluations occur. -/
theorem terminal_stored_route_checked {K : Type} [Lean.Grind.Field K]
    (nodes : List (TerminalDAGNode K)) (previousLive : List Nat)
    (previousPosition : Nat → Nat) (zeroSlot : Nat) (stored : TerminalStoredPlan)
    (checked : terminalStoredRouteCheck nodes previousLive previousPosition zeroSlot stored=true) :
    TerminalLayerRoute (fun i => nodes.getD i (.constant 0)) nodes.length
      previousLive previousPosition zeroSlot stored.plan ∧
    0<stored.gates.length ∧
    (∀ i,∀ hi : i<stored.gates.length,stored.plan.gates i=stored.gates[i]) ∧
    (∀ i∈stored.plan.live,stored.plan.position i<stored.gates.length) := by
  simp only [terminalStoredRouteCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
  obtain ⟨⟨positive,zero⟩,all⟩ := checked
  have entry := fun i hi => List.all_eq_true.mp all i hi
  have facts : ∀ i∈stored.live,i<nodes.length ∧ i<stored.positions.length ∧
      stored.plan.position i<stored.gates.length := by
    intro i hi
    have h := entry i hi
    simp only [Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.1
  refine ⟨⟨?_,zero,?_⟩,positive,?_,?_⟩
  · intro i hi
    exact (facts i hi).1
  · intro i hi
    have h := entry i hi
    simp only [Bool.and_eq_true,decide_eq_true_eq] at h
    have route := h.2
    have lookup : nodes.getD i (.constant 0)=nodes.getD i (.input 0) := by
      simp [List.getD,(facts i hi).1]
    rw [lookup]
    cases node : nodes.getD i (.input 0) with
    | constant value =>
      simp only [terminalStoredNodeCheck,node,decide_eq_true_eq] at route
      exact Or.inr route
    | input slot =>
      simp only [terminalStoredNodeCheck,node,decide_eq_true_eq] at route
      exact Or.inr route
    | binary op left right =>
      simp only [terminalStoredNodeCheck,node,Bool.or_eq_true,decide_eq_true_eq] at route
      rcases route with computed|relay
      · exact Or.inl ⟨op,left,right,rfl,computed⟩
      · exact Or.inr relay
  · intro i hi
    simp [TerminalStoredPlan.plan,List.getD,hi]
  · intro i hi
    exact (facts i hi).2.2

def terminalStoredChainCheck {K : Type} (nodes : List (TerminalDAGNode K)) :
    List Nat → (Nat → Nat) → Nat → List TerminalStoredPlan → Bool
  | _,_,_,[] => true
  | live,position,zeroSlot,stored::rest =>
      terminalStoredRouteCheck nodes live position zeroSlot stored &&
      terminalStoredChainCheck nodes stored.plan.live stored.plan.position 0 rest

theorem terminal_stored_chain_checked {K : Type} [Lean.Grind.Field K]
    (nodes : List (TerminalDAGNode K)) (live : List Nat) (position : Nat → Nat)
    (zeroSlot : Nat) (stages : List TerminalStoredPlan)
    (checked : terminalStoredChainCheck nodes live position zeroSlot stages=true) :
    TerminalFiniteRouteChain (fun i => nodes.getD i (.constant 0)) nodes.length live position zeroSlot
      (stages.map (fun stored => (stored.plan,stored.gates))) := by
  induction stages generalizing live position zeroSlot with
  | nil => trivial
  | cons stored rest ih =>
    simp only [terminalStoredChainCheck,Bool.and_eq_true] at checked
    obtain ⟨route,positive,same,bounds⟩ := terminal_stored_route_checked nodes live position zeroSlot stored checked.1
    exact ⟨route,positive,same,bounds,ih stored.plan.live stored.plan.position 0 checked.2⟩

/-- Accepted finite chain records directly supply the root-preservation route
premise. Initial placement and DAG acyclicity remain explicit interfaces. -/
theorem terminal_stored_certified_root {K : Type} [Lean.Grind.Field K]
    (inputs constants : Nat → K) (nodes : List (TerminalDAGNode K))
    (acyclic : TerminalDAGAcyclic 0 nodes) (capacity : Nat)
    (live : List Nat) (position : Nat → Nat) (zeroSlot : Nat)
    (stages : List TerminalStoredPlan)
    (initial : TerminalInitialRoute (fun i => nodes.getD i (.constant 0)) nodes.length
      capacity constants live position zeroSlot)
    (checked : terminalStoredChainCheck nodes live position zeroSlot stages=true)
    (root : Nat) (rootLive : root∈(terminalLastPlacement live position (stages.map (fun s => s.plan))).1) :
    gkrFiniteCircuit (terminalInitialValues capacity inputs constants) (stages.map (fun s => s.gates))
      ((terminalLastPlacement live position (stages.map (fun s => s.plan))).2 root)=
      terminalDAGRun inputs 0 (fun _ => 0) nodes root := by
  have chain := terminal_stored_chain_checked nodes live position zeroSlot stages checked
  simpa only [List.map_map,Function.comp_def] using terminal_finite_certified_root inputs constants nodes
    acyclic capacity live position zeroSlot (stages.map (fun s => (s.plan,s.gates)))
    initial chain root (by simpa only [List.map_map,Function.comp_def] using rootLive)

private def routeSmokeNodes : List (TerminalDAGNode Nat) := [.input 0,.binary .add 0 0]
private def routeSmokePlan : TerminalStoredPlan :=
  ⟨[1],[0,1],[⟨.add,1,1⟩,⟨.add,0,0⟩]⟩

/-- Kernel-evaluated positive route and six independent structural rejections. -/
theorem terminal_stored_route_regressions :
    terminalStoredChainCheck routeSmokeNodes [0] (fun _ => 0) 1 [routeSmokePlan]=true ∧
    terminalStoredRouteCheck routeSmokeNodes [] (fun _ => 0) 1 routeSmokePlan=false ∧
    terminalStoredRouteCheck routeSmokeNodes [0] (fun _ => 0) 1
      {routeSmokePlan with gates := [⟨.sub,1,1⟩,⟨.add,0,0⟩]}=false ∧
    terminalStoredRouteCheck routeSmokeNodes [0] (fun _ => 0) 1
      {routeSmokePlan with gates := [⟨.add,1,1⟩,⟨.sub,0,0⟩]}=false ∧
    terminalStoredRouteCheck routeSmokeNodes [0] (fun _ => 0) 1
      {routeSmokePlan with live := [2]}=false ∧
    terminalStoredRouteCheck routeSmokeNodes [0] (fun _ => 0) 1
      {routeSmokePlan with positions := [0,2]}=false ∧
    terminalStoredRouteCheck routeSmokeNodes [0] (fun _ => 0) 1
      {routeSmokePlan with positions := []}=false := by decide

end NearCompression
