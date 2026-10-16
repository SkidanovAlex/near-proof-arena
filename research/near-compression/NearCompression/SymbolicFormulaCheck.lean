import NearCompression.SymbolicCompiledCheck
import NearCompression.BusFormulaCheck
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

/-- Acyclicity depends only on binary register dependencies, not on the input
values used to specialize current/next leaves or on selector constants. -/
theorem symbolic_program_acyclic_check {K : Type} [Field K]
    (program : List (TerminalInstruction K)) (env : TerminalProgramEnvironment K)
    (placement : TerminalSymbolicPlacement K) (index : Nat) :
    terminalAcyclicCheck index (program.map (terminalProgramNode env))=
      terminalAcyclicCheck index (program.map (terminalSymbolicProgramNode placement)) := by
  induction program generalizing index with
  | nil => rfl
  | cons instruction rest ih =>
    rcases instruction with ⟨op,left,right,value⟩
    cases op <;> simp only [List.map_cons,terminalProgramNode,terminalSymbolicProgramNode,terminalAcyclicCheck,ih]

structure SymbolicFormulaTable (K : Type) where
  compiled : SymbolicCompiledTable K
  publicValues : List K
  width : Nat
  mixing : K
  residuals : List (AIRBusResidual K × Nat)
  zeroReg : Nat
  total : Nat
  steps : List AIRAccumulatorStep

def symbolicFormulaTableCheck {K : Type} [Field K] [DecidableEq K]
    (table : SymbolicFormulaTable K) : Bool :=
  table.residuals.all (fun r => airBusResidualCheck table.compiled.program table.publicValues table.width r.1 r.2) &&
  airWeightedProgramCheck table.compiled.program table.mixing (table.residuals.map Prod.snd)
    table.zeroReg table.total table.compiled.sourceRoot table.steps

def symbolicFormulaOutputs {K : Type} [Field K] (inputs : Nat → K)
    (tables : List (SymbolicFormulaTable K)) : List (K × K) :=
  tables.map (fun t =>
    (airBusMixValue (t.compiled.placement.environment inputs) t.publicValues t.mixing 1 t.residuals*
      t.compiled.entry.weight,t.compiled.entry.claim))

theorem symbolic_formula_table_value {K : Type} [Field K] [DecidableEq K]
    (table : SymbolicFormulaTable K)
    (acyclic : terminalAcyclicCheck 0
      (table.compiled.program.map (terminalSymbolicProgramNode table.compiled.placement))=true)
    (h : symbolicFormulaTableCheck table=true) :
    ∀ inputs : Nat → K,
    terminalProgramRun (table.compiled.placement.environment inputs) 0 (fun _ => 0)
      table.compiled.program table.compiled.sourceRoot=
      airBusMixValue (table.compiled.placement.environment inputs) table.publicValues table.mixing 1 table.residuals := by
  intro inputs
  simp only [symbolicFormulaTableCheck,Bool.and_eq_true] at h
  have source : terminalAcyclicCheck 0
      (table.compiled.program.map (terminalProgramNode (table.compiled.placement.environment inputs)))=true := by
    rw [symbolic_program_acyclic_check _ _ table.compiled.placement]
    exact acyclic
  rw [air_weighted_program_checked _ _ _ _ _ _ _ _ source h.2]
  exact air_bus_mix_checked _ _ _ _ _ _ _ source h.1

def symbolicFormulaCompilerCheck {K : Type} [Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (constants : Nat → K) (rho : K)
    (tables : List (SymbolicFormulaTable K)) (balance : TerminalBalanceCertificate K)
    (root zeroNode capacity : Nat) (live positions : List Nat) (zeroSlot : Nat)
    (stages : List TerminalStoredPlan) (outputSlot : Nat) : Bool :=
  symbolicCompiledCheck nodes constants rho (tables.map (fun t => t.compiled)) balance root zeroNode capacity
    live positions zeroSlot stages outputSlot && tables.all symbolicFormulaTableCheck

/-- Full finite execution equals checked mixed AIR/bus formula evaluation for
all private inputs. The supplied formula list still needs identification with
the intended AIR/bus specification; acceptance is not AIR satisfaction. -/
theorem symbolic_formula_compiler_value {K : Type} [Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (constants : Nat → K) (rho : K)
    (tables : List (SymbolicFormulaTable K)) (balance : TerminalBalanceCertificate K)
    (root zeroNode capacity : Nat) (live positions : List Nat) (zeroSlot : Nat)
    (stages : List TerminalStoredPlan) (outputSlot : Nat)
    (h : symbolicFormulaCompilerCheck nodes constants rho tables balance root zeroNode capacity
      live positions zeroSlot stages outputSlot=true) :
    ∀ inputs : Nat → K,
    gkrFiniteCircuit (terminalInitialValues capacity inputs constants) (stages.map (fun s => s.gates)) outputSlot=
      terminalResidualValue rho 1 (symbolicFormulaOutputs inputs tables) := by
  intro inputs
  simp only [symbolicFormulaCompilerCheck,Bool.and_eq_true] at h
  rw [symbolic_compiled_finite_value nodes constants rho _ balance root zeroNode capacity
    live positions zeroSlot stages outputSlot h.1 inputs]
  have checks := h.1
  simp only [symbolicCompiledCheck,Bool.and_eq_true] at checks
  congr 1
  simp only [symbolicCompiledOutputs,List.map_map,symbolicFormulaOutputs]
  apply List.map_congr_left
  intro table ht
  have member : table.compiled∈tables.map (fun t => t.compiled) := List.mem_map.mpr ⟨table,ht,rfl⟩
  have compiled := List.all_eq_true.mp checks.1.1.1.1.2 table.compiled member
  simp only [symbolicCompiledTableCheck,Bool.and_eq_true] at compiled
  have value := symbolic_formula_table_value table compiled.1 (List.all_eq_true.mp h.2 table ht) inputs
  simp only [Function.comp_apply,value]

theorem symbolic_formula_recovered_value {K : Type} [Field K] [DecidableEq K]
    (C capacity : Nat) (entries : List (GKRSourceLane × Poly K))
    (rowpoints : GKRSourceLane → Nat → K) (constants : List (Nat × K))
    (geometry : ∀ e∈entries,e.1.inputStart+e.1.width≤capacity ∧
      e.1.inputStart+e.1.nextOffset+e.1.width≤capacity)
    (constantBound : ∀ e∈constants,capacity≤e.1)
    (nodes : List (TerminalDAGNode K)) (rho : K) (tables : List (SymbolicFormulaTable K))
    (balance : TerminalBalanceCertificate K) (root zeroNode : Nat)
    (live positions : List Nat) (zeroSlot : Nat) (stages : List TerminalStoredPlan) (outputSlot : Nat)
    (checked : symbolicFormulaCompilerCheck nodes (gkrScatter constants) rho tables balance root zeroNode capacity
      live positions zeroSlot stages outputSlot=true) :
    gkrFiniteCircuit (gkrRecoveredCircuitInput C entries rowpoints constants)
      (stages.map (fun s => s.gates)) outputSlot=
      terminalResidualValue rho 1
        (symbolicFormulaOutputs (gkrScatter (recoveredPrivateSlots C entries rowpoints)) tables) := by
  rw [recovered_circuit_input_initial C capacity entries rowpoints constants geometry constantBound]
  exact symbolic_formula_compiler_value nodes (gkrScatter constants) rho tables balance root zeroNode capacity
    live positions zeroSlot stages outputSlot checked _

private def formulaSmokeNodes : List (TerminalDAGNode Rat) := [.input 0,.constant 0,.constant 1]
private def formulaSmokeTable : SymbolicFormulaTable Rat :=
  ⟨⟨⟨0,1,0,0,0⟩,
    [⟨.constant,0,0,0⟩,⟨.current,0,0,0⟩,⟨.constant,0,0,1⟩,
     ⟨.mul,2,1,0⟩,⟨.add,0,3,0⟩,⟨.add,4,0,0⟩],5,
    [⟨0,1,.constant 0⟩,⟨1,0,.input 0⟩,⟨2,2,.constant 1⟩,
     ⟨3,0,.binary .mul 2 1 2 0 .mulOneLeft⟩,⟨4,0,.binary .add 0 3 1 0 .addZeroLeft⟩,
     ⟨5,0,.binary .add 4 0 0 1 .addZeroRight⟩],
    ⟨0,1,0,2,1,2,0,0,0,.mulOneRight,.subZeroRight,.mulOneLeft⟩⟩,
   [],1,7,[(.inl (.col 0 false),1)],0,4,[⟨1,2,3,4⟩]⟩

/-- Complete formula-to-finite-circuit acceptance, with changed formula,
missing residual, final-copy and symbolic-placement failures. -/
theorem symbolic_formula_check_regressions :
    symbolicFormulaCompilerCheck formulaSmokeNodes (fun _ => 0) 11 [formulaSmokeTable]
      (.positive 0) 0 1 1 [0] [0,0,0] 1 [] 0=true ∧
    symbolicFormulaCompilerCheck formulaSmokeNodes (fun _ => 0) 11
      [{formulaSmokeTable with residuals:=[(.inl (.col 0 true),1)]}]
      (.positive 0) 0 1 1 [0] [0,0,0] 1 [] 0=false ∧
    symbolicFormulaTableCheck {formulaSmokeTable with residuals:=[]}=false ∧
    symbolicFormulaTableCheck {formulaSmokeTable with compiled:={formulaSmokeTable.compiled with sourceRoot:=4}}=false ∧
    symbolicFormulaCompilerCheck formulaSmokeNodes (fun _ => 0) 11
      [{formulaSmokeTable with compiled:={formulaSmokeTable.compiled with
        placement:={formulaSmokeTable.compiled.placement with base:=1}}}]
      (.positive 0) 0 1 1 [0] [0,0,0] 1 [] 0=false ∧
    symbolicFormulaOutputs (fun _ => (3:Rat)) [formulaSmokeTable]=[(3,0)] ∧
    symbolicFormulaOutputs (fun _ => (-7:Rat)) [formulaSmokeTable]=[(-7,0)] := by decide +kernel

end NearCompression
