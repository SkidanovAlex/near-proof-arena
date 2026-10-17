import NearCompression.TerminalSymbolicRebuild
import NearCompression.RecoveredCompiledCheck
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

structure SymbolicCompiledTable (K : Type) where
  placement : TerminalSymbolicPlacement K
  program : List (TerminalInstruction K)
  sourceRoot : Nat
  records : List (TerminalRebuildRecord K)
  entry : TerminalBatchEntry K

def symbolicCompiledTableCheck {K : Type} [Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (table : SymbolicCompiledTable K) : Bool :=
  terminalAcyclicCheck 0 (table.program.map (terminalSymbolicProgramNode table.placement)) &&
  terminalSymbolicRebuildCheck (table.program.map (terminalSymbolicProgramNode table.placement))
    nodes [] table.records table.sourceRoot table.entry.root

def symbolicCompiledOutputs {K : Type} [Field K] (inputs : Nat → K)
    (tables : List (SymbolicCompiledTable K)) : List (K × K) :=
  tables.map (fun t =>
    (terminalProgramRun (t.placement.environment inputs) 0 (fun _ => 0) t.program t.sourceRoot*t.entry.weight,t.entry.claim))

/-- This predicate contains no private input assignment. It checks the whole
compiler path, including final batching and physical finite layout. -/
def symbolicCompiledCheck {K : Type} [Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (constants : Nat → K) (rho : K)
    (tables : List (SymbolicCompiledTable K)) (balance : TerminalBalanceCertificate K)
    (root zeroNode capacity : Nat) (live positions : List Nat) (zeroSlot : Nat)
    (stages : List TerminalStoredPlan) (outputSlot : Nat) : Bool :=
  terminalStoredBundleCheck nodes capacity constants live positions zeroSlot stages root outputSlot &&
  tables.all (symbolicCompiledTableCheck nodes) &&
  terminalBatchEntriesCheck nodes rho 1 (tables.map (fun t => t.entry)) &&
  decide (balance.terms=tables.map (fun t => (t.entry.termNode,true))) &&
  terminalBalanceCheck nodes balance && terminalBatchRootCheck nodes balance.result root zeroNode

theorem symbolic_compiled_table_value {K : Type} [Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (table : SymbolicCompiledTable K)
    (acyclic : terminalAcyclicCheck 0 nodes=true)
    (h : symbolicCompiledTableCheck nodes table=true) :
    ∀ inputs : Nat → K,terminalDAGRun inputs 0 (fun _ => 0) nodes table.entry.root=
      terminalProgramRun (table.placement.environment inputs) 0 (fun _ => 0) table.program table.sourceRoot := by
  intro inputs
  simp only [symbolicCompiledTableCheck,Bool.and_eq_true] at h
  rw [terminal_symbolic_program_run]
  exact terminal_symbolic_rebuild_executed _ nodes h.1 acyclic table.records table.sourceRoot table.entry.root h.2 inputs

/-- One accepted certificate yields the complete finite-circuit residual
identity for every private assignment; no per-assignment checker premise. -/
theorem symbolic_compiled_finite_value {K : Type} [Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (constants : Nat → K) (rho : K)
    (tables : List (SymbolicCompiledTable K)) (balance : TerminalBalanceCertificate K)
    (root zeroNode capacity : Nat) (live positions : List Nat) (zeroSlot : Nat)
    (stages : List TerminalStoredPlan) (outputSlot : Nat)
    (h : symbolicCompiledCheck nodes constants rho tables balance root zeroNode capacity
      live positions zeroSlot stages outputSlot=true) :
    ∀ inputs : Nat → K,
    gkrFiniteCircuit (terminalInitialValues capacity inputs constants) (stages.map (fun s => s.gates)) outputSlot=
      terminalResidualValue rho 1 (symbolicCompiledOutputs inputs tables) := by
  intro inputs
  simp only [symbolicCompiledCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨bundle,programs⟩,entries⟩,terms⟩,balanced⟩,final⟩ := h
  have acyclic : terminalAcyclicCheck 0 nodes=true := by
    simp only [terminalStoredBundleCheck,Bool.and_eq_true] at bundle
    exact bundle.1.1.1
  rw [terminal_checked_bundle_root inputs constants nodes capacity live positions zeroSlot stages root outputSlot bundle]
  rw [terminal_batch_checked_value nodes inputs rho (tables.map (fun t => t.entry)) balance root zeroNode
    acyclic entries (by simpa only [List.map_map,Function.comp_def] using terms) balanced final]
  congr 1
  simp only [List.map_map,symbolicCompiledOutputs]
  apply List.map_congr_left
  intro table ht
  have value := symbolic_compiled_table_value nodes table acyclic (List.all_eq_true.mp programs table ht) inputs
  simp only [Function.comp_apply,value]

/-- The same input-independent certificate applies to the actual decoded tuple
construction used by GKR, under support separation. This does not extract a
tuple from a commitment or certify a quantum probability bound. -/
theorem symbolic_compiled_recovered_value {K : Type} [Field K] [DecidableEq K]
    (C capacity : Nat) (entries : List (GKRSourceLane × Poly K))
    (rowpoints : GKRSourceLane → Nat → K) (constants : List (Nat × K))
    (geometry : ∀ e∈entries,e.1.inputStart+e.1.width≤capacity ∧
      e.1.inputStart+e.1.nextOffset+e.1.width≤capacity)
    (constantBound : ∀ e∈constants,capacity≤e.1)
    (nodes : List (TerminalDAGNode K)) (rho : K) (tables : List (SymbolicCompiledTable K))
    (balance : TerminalBalanceCertificate K) (root zeroNode : Nat)
    (live positions : List Nat) (zeroSlot : Nat) (stages : List TerminalStoredPlan) (outputSlot : Nat)
    (checked : symbolicCompiledCheck nodes (gkrScatter constants) rho tables balance root zeroNode capacity
      live positions zeroSlot stages outputSlot=true) :
    gkrFiniteCircuit (gkrRecoveredCircuitInput C entries rowpoints constants)
      (stages.map (fun s => s.gates)) outputSlot=
      terminalResidualValue rho 1
        (symbolicCompiledOutputs (gkrScatter (recoveredPrivateSlots C entries rowpoints)) tables) := by
  rw [recovered_circuit_input_initial C capacity entries rowpoints constants geometry constantBound]
  exact symbolic_compiled_finite_value nodes (gkrScatter constants) rho tables balance root zeroNode capacity
    live positions zeroSlot stages outputSlot checked _

private def symbolicSmokeNodes : List (TerminalDAGNode Rat) := [.input 0,.constant 1,.constant 0]
private def symbolicSmokeTable : SymbolicCompiledTable Rat :=
  ⟨⟨0,1,0,0,0⟩,[⟨.current,0,0,0⟩],0,[⟨0,0,.input 0⟩],
   ⟨0,1,0,1,2,1,0,0,0,.mulOneRight,.subZeroRight,.mulOneLeft⟩⟩

theorem symbolic_compiled_check_regressions :
    symbolicCompiledCheck symbolicSmokeNodes (fun _ => 0) 7 [symbolicSmokeTable]
      (.positive 0) 0 2 1 [0] [0,0,0] 2 [] 0=true ∧
    symbolicCompiledCheck symbolicSmokeNodes (fun _ => 0) 7
      [{symbolicSmokeTable with placement:={symbolicSmokeTable.placement with base:=1}}]
      (.positive 0) 0 2 1 [0] [0,0,0] 2 [] 0=false ∧
    symbolicCompiledCheck symbolicSmokeNodes (fun _ => 0) 7
      [{symbolicSmokeTable with records:=[]}]
      (.positive 0) 0 2 1 [0] [0,0,0] 2 [] 0=false ∧
    symbolicCompiledCheck symbolicSmokeNodes (fun _ => 0) 7 [symbolicSmokeTable]
      (.positive 0) 0 2 1 [0] [0,0,0] 2 [] 1=false ∧
    symbolicCompiledOutputs (fun _ => (3:Rat)) [symbolicSmokeTable]=[(3,0)] ∧
    symbolicCompiledOutputs (fun _ => (-7:Rat)) [symbolicSmokeTable]=[(-7,0)] := by decide +kernel

end NearCompression
