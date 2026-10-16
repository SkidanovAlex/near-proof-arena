import NearCompression.TerminalBatchCheck
namespace NearCompression

structure TerminalCompiledTable (K : Type) where
  environment : TerminalProgramEnvironment K
  program : List (TerminalInstruction K)
  sourceRoot : Nat
  records : List (TerminalRebuildRecord K)
  entry : TerminalBatchEntry K

def terminalCompiledTableCheck {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (inputs : Nat → K) (table : TerminalCompiledTable K) : Bool :=
  terminalAcyclicCheck 0 (table.program.map (terminalProgramNode table.environment)) &&
  terminalRebuildRecordsCheck (table.program.map (terminalProgramNode table.environment))
    nodes inputs [] table.records table.sourceRoot table.entry.root

def terminalCompiledDAGCheck {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (inputs : Nat → K) (rho : K)
    (tables : List (TerminalCompiledTable K)) (balance : TerminalBalanceCertificate K)
    (root zeroNode : Nat) : Bool :=
  terminalAcyclicCheck 0 nodes && tables.all (terminalCompiledTableCheck nodes inputs) &&
  terminalBatchEntriesCheck nodes rho 1 (tables.map (fun t => t.entry)) &&
  decide (balance.terms=tables.map (fun t => (t.entry.termNode,true))) &&
  terminalBalanceCheck nodes balance && terminalBatchRootCheck nodes balance.result root zeroNode

def terminalCompiledOutputs {K : Type} [Lean.Grind.Field K]
    (tables : List (TerminalCompiledTable K)) : List (K × K) :=
  tables.map (fun t =>
    (terminalProgramRun t.environment 0 (fun _ => 0) t.program t.sourceRoot*t.entry.weight,t.entry.claim))

theorem terminal_compiled_table_checked {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (inputs : Nat → K) (table : TerminalCompiledTable K)
    (acyclic : terminalAcyclicCheck 0 nodes=true)
    (h : terminalCompiledTableCheck nodes inputs table=true) :
    terminalDAGRun inputs 0 (fun _ => 0) nodes table.entry.root=
      terminalProgramRun table.environment 0 (fun _ => 0) table.program table.sourceRoot := by
  simp only [terminalCompiledTableCheck,Bool.and_eq_true] at h
  exact terminal_program_rebuilt_value table.environment table.program nodes inputs
    (terminal_acyclic_checked _ 0 h.1) (terminal_acyclic_checked nodes 0 acyclic)
    table.sourceRoot table.entry.root
    (terminal_rebuild_records_checked _ nodes inputs table.records [] table.sourceRoot table.entry.root
      (by intro p hp; simp at hp) h.2)

/-- All reconstruction and batching premises are derived from one Boolean
acceptance. Source programs and environments are explicit input data, not yet
identified with the AIR compiler or extracted committed trace. -/
theorem terminal_compiled_dag_checked {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (inputs : Nat → K) (rho : K)
    (tables : List (TerminalCompiledTable K)) (balance : TerminalBalanceCertificate K)
    (root zeroNode : Nat) (h : terminalCompiledDAGCheck nodes inputs rho tables balance root zeroNode=true) :
    terminalDAGRun inputs 0 (fun _ => 0) nodes root=
      terminalResidualValue rho 1 (terminalCompiledOutputs tables) := by
  simp only [terminalCompiledDAGCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨acyclic,programs⟩,entries⟩,terms⟩,balanced⟩,final⟩ := h
  have bound := terminal_batch_checked_value nodes inputs rho (tables.map (fun t => t.entry))
    balance root zeroNode acyclic entries (by simpa only [List.map_map,Function.comp_def] using terms) balanced final
  rw [bound]
  congr 1
  simp only [List.map_map,terminalCompiledOutputs]
  apply List.map_congr_left
  intro table ht
  have value := terminal_compiled_table_checked nodes inputs table acyclic (List.all_eq_true.mp programs table ht)
  simp only [Function.comp_apply,value]

def terminalCompiledFiniteCheck {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (inputs constants : Nat → K) (rho : K)
    (tables : List (TerminalCompiledTable K)) (balance : TerminalBalanceCertificate K)
    (root zeroNode capacity : Nat) (live positions : List Nat) (zeroSlot : Nat)
    (stages : List TerminalStoredPlan) (outputSlot : Nat) : Bool :=
  terminalStoredBundleCheck nodes capacity constants live positions zeroSlot stages root outputSlot &&
    terminalCompiledDAGCheck nodes inputs rho tables balance root zeroNode

/-- Finite GKR execution equals the exact weighted residual of independently
executed source programs. No node equations, reconstruction routes, layer
routes or intermediate equality premises are assumed. -/
theorem terminal_compiled_finite_checked {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (inputs constants : Nat → K) (rho : K)
    (tables : List (TerminalCompiledTable K)) (balance : TerminalBalanceCertificate K)
    (root zeroNode capacity : Nat) (live positions : List Nat) (zeroSlot : Nat)
    (stages : List TerminalStoredPlan) (outputSlot : Nat)
    (h : terminalCompiledFiniteCheck nodes inputs constants rho tables balance root zeroNode capacity
      live positions zeroSlot stages outputSlot=true) :
    gkrFiniteCircuit (terminalInitialValues capacity inputs constants) (stages.map (fun s => s.gates)) outputSlot=
      terminalResidualValue rho 1 (terminalCompiledOutputs tables) := by
  simp only [terminalCompiledFiniteCheck,Bool.and_eq_true] at h
  rw [terminal_checked_bundle_root inputs constants nodes capacity live positions zeroSlot stages root outputSlot h.1]
  exact terminal_compiled_dag_checked nodes inputs rho tables balance root zeroNode h.2

private def compiledSmokeNodes : List (TerminalDAGNode Rat) := [.input 0,.constant 1,.constant 0]
private def compiledSmokeTable : TerminalCompiledTable Rat :=
  ⟨⟨(fun _ => 5),(fun _ => 0),0,0,0⟩,[⟨.current,0,0,0⟩],0,[⟨0,0,.input 0⟩],
   ⟨0,1,0,1,2,1,0,0,0,.mulOneRight,.subZeroRight,.mulOneLeft⟩⟩

/-- The complete finite checker accepts an optimized one-input program and
rejects mismatched input, missing reconstruction, changed claim, wrong output
slot, inconsistent balance and omitted program. -/
theorem terminal_compiled_check_regressions :
    terminalCompiledFiniteCheck compiledSmokeNodes (fun _ => 5) (fun _ => 0) 7
      [compiledSmokeTable] (.positive 0) 0 2 1 [0] [0,0,0] 2 [] 0=true ∧
    terminalCompiledFiniteCheck compiledSmokeNodes (fun _ => 6) (fun _ => 0) 7
      [compiledSmokeTable] (.positive 0) 0 2 1 [0] [0,0,0] 2 [] 0=false ∧
    terminalCompiledDAGCheck compiledSmokeNodes (fun _ => 5) 7
      [{compiledSmokeTable with records:=[]}] (.positive 0) 0 2=false ∧
    terminalCompiledDAGCheck compiledSmokeNodes (fun _ => 5) 7
      [{compiledSmokeTable with entry:={compiledSmokeTable.entry with claim:=1}}] (.positive 0) 0 2=false ∧
    terminalCompiledFiniteCheck compiledSmokeNodes (fun _ => 5) (fun _ => 0) 7
      [compiledSmokeTable] (.positive 0) 0 2 1 [0] [0,0,0] 2 [] 1=false ∧
    terminalCompiledDAGCheck compiledSmokeNodes (fun _ => 5) 7
      [compiledSmokeTable] (.positive 1) 0 2=false ∧
    terminalCompiledDAGCheck compiledSmokeNodes (fun _ => 5) 7 [] (.positive 0) 0 2=false := by decide +kernel

end NearCompression
