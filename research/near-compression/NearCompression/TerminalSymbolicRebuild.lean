import NearCompression.TerminalRebuildCheck
namespace NearCompression
open Lean.Grind

def terminalSymbolicRebuildRecordCheck {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (source target : List (TerminalDAGNode K))
    (known : List (Nat × Nat)) (record : TerminalRebuildRecord K) : Bool :=
  decide (record.source<source.length ∧ record.target<target.length) &&
  match record.recipe with
  | .constant value => decide (source.getD record.source (.constant 0)=.constant value ∧
      target.getD record.target (.constant 0)=.constant value)
  | .input slot => decide (source.getD record.source (.constant 0)=.input slot ∧
      target.getD record.target (.constant 0)=.input slot)
  | .binary op left right x y w =>
      decide (source.getD record.source (.constant 0)=.binary op left right ∧
        (left,x)∈known ∧ (right,y)∈known) &&
      terminalStoredArithmeticCheck target op x y record.target w
  | .expanded tree mapping balance =>
      decide (tree.root=record.source ∧ tree.sign=true ∧ balance.result=record.target ∧
        balance.terms=tree.terms.map (fun t => (mapping.getD t.1 0,t.2))) &&
      tree.terms.all (fun t => decide (t.1<mapping.length ∧ (t.1,mapping.getD t.1 0)∈known)) &&
      terminalExpansionCheck source tree && terminalBalanceCheck target balance

/-- Input nodes are bound by slot identity, not by coincidental equality of
values in one assignment. The same certificate works for arbitrary inputs. -/
theorem terminal_symbolic_record_value {K : Type} [Field K] [DecidableEq K]
    (source target : List (TerminalDAGNode K)) (inputs sourceValues targetValues : Nat → K)
    (sourceEquations : ∀ i,sourceValues i=terminalNodeValue inputs sourceValues (source.getD i (.constant 0)))
    (targetEquations : ∀ i,targetValues i=terminalNodeValue inputs targetValues (target.getD i (.constant 0)))
    (known : List (Nat × Nat)) (record : TerminalRebuildRecord K)
    (prior : ∀ p∈known,targetValues p.2=sourceValues p.1)
    (checked : terminalSymbolicRebuildRecordCheck source target known record=true) :
    targetValues record.target=sourceValues record.source := by
  rcases record with ⟨i,z,recipe⟩
  have hs := sourceEquations i
  have ht := targetEquations z
  cases recipe with
  | constant value =>
    simp only [terminalSymbolicRebuildRecordCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
    simp only [checked.2.1,terminalNodeValue] at hs
    simp only [checked.2.2,terminalNodeValue] at ht
    exact ht.trans hs.symm
  | input slot =>
    simp only [terminalSymbolicRebuildRecordCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
    simp only [checked.2.1,terminalNodeValue] at hs
    simp only [checked.2.2,terminalNodeValue] at ht
    exact ht.trans hs.symm
  | binary op left right x y w =>
    simp only [terminalSymbolicRebuildRecordCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
    have route := (terminal_stored_arithmetic_checked target op x y z w checked.2.2).2
    have value := terminal_arithmetic_route_value _ inputs targetValues targetEquations op x y z route
    rw [prior (left,x) checked.2.1.2.1,prior (right,y) checked.2.1.2.2] at value
    simp only [checked.2.1.1,terminalNodeValue] at hs
    exact value.trans hs.symm
  | expanded tree mapping balance =>
    simp only [terminalSymbolicRebuildRecordCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
    obtain ⟨_,⟨⟨⟨⟨root,sign,result,terms⟩,leaves⟩,expand⟩,balanced⟩⟩ := checked
    have expansion := terminal_expansion_checked source tree expand
    rw [root,sign] at expansion
    have route := terminal_balance_checked target balance balanced
    rw [result,terms] at route
    apply terminal_rebuilt_expansion_value inputs sourceValues inputs targetValues _ _
      sourceEquations targetEquations i z tree.terms (fun j => mapping.getD j 0) expansion ?_ route
    intro t ht
    have leaf := List.all_eq_true.mp leaves t ht
    simp only [decide_eq_true_eq] at leaf
    exact prior _ leaf.2

def terminalSymbolicRebuildCheck {K : Type} [Field K] [DecidableEq K]
    (source target : List (TerminalDAGNode K)) :
    List (Nat × Nat) → List (TerminalRebuildRecord K) → Nat → Nat → Bool
  | known,[],i,z => decide ((i,z)∈known)
  | known,record::rest,i,z => terminalSymbolicRebuildRecordCheck source target known record &&
      terminalSymbolicRebuildCheck source target ((record.source,record.target)::known) rest i z

theorem terminal_symbolic_records_value {K : Type} [Field K] [DecidableEq K]
    (source target : List (TerminalDAGNode K)) (inputs sourceValues targetValues : Nat → K)
    (sourceEquations : ∀ i,sourceValues i=terminalNodeValue inputs sourceValues (source.getD i (.constant 0)))
    (targetEquations : ∀ i,targetValues i=terminalNodeValue inputs targetValues (target.getD i (.constant 0)))
    (records : List (TerminalRebuildRecord K)) (known : List (Nat × Nat)) (i z : Nat)
    (prior : ∀ p∈known,targetValues p.2=sourceValues p.1)
    (checked : terminalSymbolicRebuildCheck source target known records i z=true) :
    targetValues z=sourceValues i := by
  induction records generalizing known with
  | nil =>
    simp only [terminalSymbolicRebuildCheck,decide_eq_true_eq] at checked
    exact prior _ checked
  | cons record rest ih =>
    simp only [terminalSymbolicRebuildCheck,Bool.and_eq_true] at checked
    apply ih ((record.source,record.target)::known) ?_ checked.2
    intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · subst p
      exact terminal_symbolic_record_value source target inputs sourceValues targetValues
        sourceEquations targetEquations known record prior checked.1
    · exact prior p hp

theorem terminal_symbolic_rebuild_executed {K : Type} [Field K] [DecidableEq K]
    (source target : List (TerminalDAGNode K))
    (sourceAcyclic : terminalAcyclicCheck 0 source=true)
    (targetAcyclic : terminalAcyclicCheck 0 target=true)
    (records : List (TerminalRebuildRecord K)) (i z : Nat)
    (checked : terminalSymbolicRebuildCheck source target [] records i z=true) :
    ∀ inputs : Nat → K,terminalDAGRun inputs 0 (fun _ => 0) target z=
      terminalDAGRun inputs 0 (fun _ => 0) source i := by
  intro inputs
  exact terminal_symbolic_records_value source target inputs _ _
    (terminal_dag_total_equations inputs source (terminal_acyclic_checked source 0 sourceAcyclic))
    (terminal_dag_total_equations inputs target (terminal_acyclic_checked target 0 targetAcyclic))
    records [] i z (by intro p hp; simp at hp) checked

structure TerminalSymbolicPlacement (K : Type) where
  base : Nat
  nextOffset : Nat
  first : K
  last : K
  transition : K

def TerminalSymbolicPlacement.environment {K : Type} (p : TerminalSymbolicPlacement K)
    (inputs : Nat → K) : TerminalProgramEnvironment K :=
  ⟨(fun c => inputs (p.base+c)),(fun c => inputs (p.base+p.nextOffset+c)),p.first,p.last,p.transition⟩

def terminalSymbolicProgramNode {K : Type} (p : TerminalSymbolicPlacement K)
    (instruction : TerminalInstruction K) : TerminalDAGNode K :=
  match instruction.opcode with
  | .constant => .constant instruction.constant
  | .current => .input (p.base+instruction.left)
  | .next => .input (p.base+p.nextOffset+instruction.left)
  | .first => .constant p.first | .last => .constant p.last | .transition => .constant p.transition
  | .add => .binary .add instruction.left instruction.right
  | .sub => .binary .sub instruction.left instruction.right
  | .mul => .binary .mul instruction.left instruction.right

theorem terminal_symbolic_instruction_value {K : Type} [Field K]
    (placement : TerminalSymbolicPlacement K) (inputs registers : Nat → K)
    (instruction : TerminalInstruction K) :
    terminalNodeValue inputs registers (terminalSymbolicProgramNode placement instruction)=
      terminalProgramInstructionValue (placement.environment inputs) registers instruction := by
  rcases instruction with ⟨op,left,right,value⟩
  cases op <;> rfl

theorem terminal_symbolic_program_run {K : Type} [Field K]
    (placement : TerminalSymbolicPlacement K) (inputs registers : Nat → K)
    (program : List (TerminalInstruction K)) (index : Nat) :
    terminalProgramRun (placement.environment inputs) index registers program=
      terminalDAGRun inputs index registers (program.map (terminalSymbolicProgramNode placement)) := by
  induction program generalizing index registers with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [terminalProgramRun,List.map_cons,terminalDAGRun,terminal_symbolic_instruction_value,ih]

/-- One symbolic reconstruction and finite layout certificate establishes source
program equality for every input assignment, including recovered PCS inputs.
Constants/selectors and placement remain fixed explicit compiler parameters. -/
theorem terminal_symbolic_compiled_program {K : Type} [Field K] [DecidableEq K]
    (placement : TerminalSymbolicPlacement K) (program : List (TerminalInstruction K))
    (nodes : List (TerminalDAGNode K)) (constants : Nat → K)
    (sourceRoot targetRoot capacity : Nat) (live positions : List Nat) (zeroSlot : Nat)
    (stages : List TerminalStoredPlan) (outputSlot : Nat) (records : List (TerminalRebuildRecord K))
    (sourceCheck : terminalAcyclicCheck 0 (program.map (terminalSymbolicProgramNode placement))=true)
    (bundleCheck : terminalStoredBundleCheck nodes capacity constants live positions zeroSlot stages targetRoot outputSlot=true)
    (rebuildCheck : terminalSymbolicRebuildCheck (program.map (terminalSymbolicProgramNode placement))
      nodes [] records sourceRoot targetRoot=true) :
    ∀ inputs : Nat → K,
    gkrFiniteCircuit (terminalInitialValues capacity inputs constants) (stages.map (fun s => s.gates)) outputSlot=
      terminalProgramRun (placement.environment inputs) 0 (fun _ => 0) program sourceRoot := by
  intro inputs
  rw [terminal_checked_bundle_root inputs constants nodes capacity live positions zeroSlot stages targetRoot outputSlot bundleCheck]
  rw [terminal_symbolic_program_run]
  have targetCheck : terminalAcyclicCheck 0 nodes=true := by
    simp only [terminalStoredBundleCheck,Bool.and_eq_true] at bundleCheck
    exact bundleCheck.1.1.1
  exact terminal_symbolic_rebuild_executed _ nodes sourceCheck targetCheck records sourceRoot targetRoot rebuildCheck inputs

/-- Equal sample values do not justify substituting physical input identities.
The symbolic checker also distinguishes input leaves from literal constants. -/
theorem terminal_symbolic_rebuild_regressions :
    terminalSymbolicRebuildCheck ([.input 0] : List (TerminalDAGNode Rat)) [.input 0]
      [] [⟨0,0,.input 0⟩] 0 0=true ∧
    terminalSymbolicRebuildCheck ([.input 0] : List (TerminalDAGNode Rat)) [.input 1]
      [] [⟨0,0,.input 1⟩] 0 0=false ∧
    terminalSymbolicRebuildCheck ([.input 0] : List (TerminalDAGNode Rat)) [.constant 5]
      [] [⟨0,0,.constant 5⟩] 0 0=false ∧
    terminalRebuildRecordsCheck ([.constant 5] : List (TerminalDAGNode Rat)) [.input 1] (fun _ => 5)
      [] [⟨0,0,.input 1⟩] 0 0=true ∧
    terminalSymbolicRebuildCheck ([.input 0,.input 1,.binary .mul 0 1] : List (TerminalDAGNode Rat))
      [.input 0,.input 1,.binary .mul 0 1] []
      [⟨0,0,.input 0⟩,⟨1,1,.input 1⟩,⟨2,2,.binary .mul 0 1 0 1 .direct⟩] 2 2=true ∧
    terminalSymbolicRebuildCheck ([.input 0] : List (TerminalDAGNode Rat)) [.input 0]
      [] [] 0 0=false := by decide +kernel

end NearCompression
