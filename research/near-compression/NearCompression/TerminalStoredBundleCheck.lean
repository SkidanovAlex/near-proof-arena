import NearCompression.TerminalStoredRouteCheck
namespace NearCompression

def terminalAcyclicCheck {K : Type} : Nat → List (TerminalDAGNode K) → Bool
  | _,[] => true
  | index,node::rest => (match node with
      | .binary _ left right => decide (left<index ∧ right<index)
      | _ => true) && terminalAcyclicCheck (index+1) rest

theorem terminal_acyclic_checked {K : Type} [Lean.Grind.Field K]
    (nodes : List (TerminalDAGNode K)) (index : Nat)
    (checked : terminalAcyclicCheck index nodes=true) : TerminalDAGAcyclic index nodes := by
  induction nodes generalizing index with
  | nil => trivial
  | cons node rest ih =>
    simp only [terminalAcyclicCheck,Bool.and_eq_true] at checked
    refine ⟨?_,ih (index+1) checked.2⟩
    cases node with
    | constant _ => trivial
    | input _ => trivial
    | binary _ left right =>
      change left<index ∧ right<index
      exact of_decide_eq_true checked.1

def terminalInitialNodeCheck {K : Type} [Zero K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (capacity : Nat) (constants : Nat → K)
    (positions : List Nat) (i : Nat) : Bool :=
  match nodes.getD i (.input 0) with
  | .input slot => decide (slot<capacity ∧ positions.getD i 0=slot)
  | .constant value => decide (capacity≤positions.getD i 0 ∧ constants (positions.getD i 0)=value)
  | .binary _ _ _ => false

def terminalInitialStoredCheck {K : Type} [Zero K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (capacity : Nat) (constants : Nat → K)
    (live positions : List Nat) (zeroSlot : Nat) : Bool :=
  decide (capacity≤zeroSlot ∧ constants zeroSlot=0) &&
  live.all (fun i => decide (i<nodes.length ∧ i<positions.length) &&
    terminalInitialNodeCheck nodes capacity constants positions i)

theorem terminal_initial_stored_checked {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (capacity : Nat) (constants : Nat → K)
    (live positions : List Nat) (zeroSlot : Nat)
    (checked : terminalInitialStoredCheck nodes capacity constants live positions zeroSlot=true) :
    TerminalInitialRoute (fun i => nodes.getD i (.constant 0)) nodes.length capacity constants live
      (fun i => positions.getD i 0) zeroSlot := by
  simp only [terminalInitialStoredCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
  have facts : ∀ i∈live,(i<nodes.length ∧ i<positions.length) ∧
      terminalInitialNodeCheck nodes capacity constants positions i=true := by
    intro i hi
    simpa only [Bool.and_eq_true,decide_eq_true_eq] using List.all_eq_true.mp checked.2 i hi
  refine ⟨?_,checked.1.1,checked.1.2,?_⟩
  · intro i hi; exact (facts i hi).1.1
  · intro i hi
    have h := (facts i hi).2
    have lookup : nodes.getD i (.constant 0)=nodes.getD i (.input 0) := by
      simp [List.getD,(facts i hi).1.1]
    rw [lookup]
    cases node : nodes.getD i (.input 0) with
    | input slot =>
      simp only [terminalInitialNodeCheck,node,decide_eq_true_eq] at h
      exact Or.inl ⟨slot,rfl,h⟩
    | constant value =>
      simp only [terminalInitialNodeCheck,node,decide_eq_true_eq] at h
      exact Or.inr ⟨value,rfl,h⟩
    | binary op left right => simp only [terminalInitialNodeCheck,node,Bool.false_eq_true] at h

def terminalStoredBundleCheck {K : Type} [Zero K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (capacity : Nat) (constants : Nat → K)
    (live positions : List Nat) (zeroSlot : Nat) (stages : List TerminalStoredPlan)
    (root outputSlot : Nat) : Bool :=
  terminalAcyclicCheck 0 nodes && terminalInitialStoredCheck nodes capacity constants live positions zeroSlot &&
  terminalStoredChainCheck nodes live (fun i => positions.getD i 0) zeroSlot stages &&
  let final := terminalLastPlacement live (fun i => positions.getD i 0) (stages.map (fun s => s.plan))
  decide (root∈final.1 ∧ final.2 root=outputSlot)

/-- One executable bundle check establishes finite root preservation for EVERY
private input. Acyclicity, initial placement, routing and root liveness are
all derived from checker acceptance, not separately assumed. -/
theorem terminal_checked_bundle_root {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (inputs constants : Nat → K) (nodes : List (TerminalDAGNode K)) (capacity : Nat)
    (live positions : List Nat) (zeroSlot : Nat) (stages : List TerminalStoredPlan)
    (root outputSlot : Nat)
    (checked : terminalStoredBundleCheck nodes capacity constants live positions zeroSlot stages root outputSlot=true) :
    gkrFiniteCircuit (terminalInitialValues capacity inputs constants) (stages.map (fun s => s.gates)) outputSlot=
      terminalDAGRun inputs 0 (fun _ => 0) nodes root := by
  simp only [terminalStoredBundleCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
  obtain ⟨⟨⟨acyclic,initial⟩,chain⟩,liveRoot,slot⟩ := checked
  rw [←slot]
  exact terminal_stored_certified_root inputs constants nodes (terminal_acyclic_checked nodes 0 acyclic)
    capacity live (fun i => positions.getD i 0) zeroSlot stages
    (terminal_initial_stored_checked nodes capacity constants live positions zeroSlot initial) chain root liveRoot

private def bundleSmokeNodes : List (TerminalDAGNode Nat) :=
  [.constant 3,.input 0,.binary .add 0 1]
private def bundleSmokeStages : List TerminalStoredPlan :=
  [⟨[2],[0,0,1],[⟨.add,2,2⟩,⟨.add,1,0⟩]⟩]

/-- Kernel-evaluated complete bundle and failures in the new boundary checks. -/
theorem terminal_stored_bundle_regressions :
    terminalStoredBundleCheck bundleSmokeNodes 1 (fun i => if i=1 then 3 else 0)
      [0,1] [1,0,0] 2 bundleSmokeStages 2 1=true ∧
    terminalStoredBundleCheck bundleSmokeNodes 1 (fun _ => 0)
      [0,1] [1,0,0] 2 bundleSmokeStages 2 1=false ∧
    terminalStoredBundleCheck bundleSmokeNodes 1 (fun i => if i=1 then 3 else 0)
      [0,1] [1,1,0] 2 bundleSmokeStages 2 1=false ∧
    terminalStoredBundleCheck bundleSmokeNodes 1 (fun i => if i=1 then 3 else 1)
      [0,1] [1,0,0] 2 bundleSmokeStages 2 1=false ∧
    terminalStoredBundleCheck [.constant 3,.input 0,.binary .add 2 1] 1
      (fun i => if i=1 then 3 else 0) [0,1] [1,0,0] 2 bundleSmokeStages 2 1=false := by decide

end NearCompression
