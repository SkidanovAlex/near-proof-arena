import NearCompression.TerminalSemanticOutputs
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- Witness data may depend on rho. Semantic tables are bound separately. -/
structure TerminalCompilerWitness (K : Type) where
  constants : List (Nat × K)
  nodes : List (TerminalDAGNode K)
  tables : List (SymbolicFormulaTable K)
  balance : TerminalBalanceCertificate K
  root : Nat
  zeroNode : Nat
  live : List Nat
  positions : List Nat
  zeroSlot : Nat
  stages : List TerminalStoredPlan
  outputSlot : Nat

def terminalCompilerWitnessCheck {K : Type} [Field K] [DecidableEq K]
    (capacity : Nat) (rho : K) (w : TerminalCompilerWitness K) : Bool :=
  symbolicFormulaCompilerCheck w.nodes (gkrScatter w.constants) rho w.tables w.balance
    w.root w.zeroNode capacity w.live w.positions w.zeroSlot w.stages w.outputSlot

def recoveredWitnessValue {K : Type} [Field K] (C : Nat)
    (entries : List (GKRSourceLane × Poly K)) (layout : GKRJointLayout)
    (history : List K) (w : TerminalCompilerWitness K) : K :=
  gkrFiniteCircuit (gkrRecoveredCircuitInput C entries (gkrHistoryRowpoints layout history) w.constants)
    (w.stages.map (fun s => s.gates)) w.outputSlot

/-- The actual finite circuit on recovered source inputs computes the fixed
semantic batch. No circuit evaluation equality is an assumption. -/
theorem checked_semantic_circuit_value {K : Type} [Field K] [DecidableEq K]
    (C capacity : Nat) (metadata : List GKRTableMetadata) (entries : List (GKRSourceLane × Poly K))
    (decoded : GKRTableMetadata → Nat → Nat → K)
    (agreement : ∀ table∈metadata,∀ placement : TerminalSymbolicPlacement K,
      symbolicPlacementMetadataCheck placement table=true → ∀ rowpoints : GKRSourceLane → Nat → K,
        TerminalEnvironmentAgreement (table.sourceWidth+table.auxiliaryWidth)
          (placement.environment (gkrScatter (recoveredPrivateSlots C entries rowpoints)))
          (decodedColumnEnvironment table placement (decoded table) rowpoints))
    (layout : GKRJointLayout) (history : List K) (rho : K) (w : TerminalCompilerWitness K)
    (metadataOf : SymbolicFormulaTable K → GKRTableMetadata) (meanings : List (TerminalTableMeaning K))
    (binding : w.tables.map (terminalTableMeaning metadataOf)=meanings)
    (geometry : ∀ e∈entries,e.1.inputStart+e.1.width≤capacity ∧ e.1.inputStart+e.1.nextOffset+e.1.width≤capacity)
    (constantBound : ∀ e∈w.constants,capacity≤e.1)
    (members : ∀ t∈w.tables,metadataOf t∈metadata)
    (placements : ∀ t∈w.tables,symbolicPlacementMetadataCheck t.compiled.placement (metadataOf t)=true)
    (selectors : ∀ t∈w.tables,symbolicSelectorCheck (metadataOf t).rowLog t.compiled.placement
      (gkrTableHistoryPoint (metadataOf t) history)=true)
    (widths : ∀ t∈w.tables,t.width≤(metadataOf t).sourceWidth+(metadataOf t).auxiliaryWidth)
    (checked : terminalCompilerWitnessCheck capacity rho w=true) :
    recoveredWitnessValue C entries layout history w=
      terminalResidualValue rho 1 (terminalMeaningOutputs decoded history meanings) := by
  have tableChecks := checked
  simp only [terminalCompilerWitnessCheck,symbolicFormulaCompilerCheck,Bool.and_eq_true] at tableChecks
  unfold recoveredWitnessValue
  rw [symbolic_formula_recovered_value C capacity entries _ w.constants geometry constantBound
    w.nodes rho w.tables w.balance w.root w.zeroNode w.live w.positions w.zeroSlot w.stages w.outputSlot checked,
    preselected_semantic_outputs C metadata entries decoded agreement layout history w.tables metadataOf meanings
      binding members placements selectors widths tableChecks.2]

/-- Checked rho-dependent circuits inherit cancellation bounds on the same
fixed decoded source and semantic list. All executable checker obligations
are explicit; no-representative and computational security remain separate. -/
theorem checked_semantic_circuit_cancellation {K : Type} [Field K] [DecidableEq K]
    (C capacity : Nat) (metadata : List GKRTableMetadata) (entries : List (GKRSourceLane × Poly K))
    (decoded : GKRTableMetadata → Nat → Nat → K)
    (agreement : ∀ table∈metadata,∀ placement : TerminalSymbolicPlacement K,
      symbolicPlacementMetadataCheck placement table=true → ∀ rowpoints : GKRSourceLane → Nat → K,
        TerminalEnvironmentAgreement (table.sourceWidth+table.auxiliaryWidth)
          (placement.environment (gkrScatter (recoveredPrivateSlots C entries rowpoints)))
          (decodedColumnEnvironment table placement (decoded table) rowpoints))
    (layout : GKRJointLayout) (history : List K) (witness : K → TerminalCompilerWitness K)
    (metadataOf : SymbolicFormulaTable K → GKRTableMetadata) (meanings : List (TerminalTableMeaning K))
    (lane : Nat) (positive : 0<(terminalMeaningOutputs decoded history meanings).length)
    (wrong : ((terminalMeaningOutputs decoded history meanings).map Prod.fst).getD lane 0≠
      ((terminalMeaningOutputs decoded history meanings).map Prod.snd).getD lane 0)
    (sample : List K) (distinct : sample.Nodup)
    (geometry : ∀ e∈entries,e.1.inputStart+e.1.width≤capacity ∧ e.1.inputStart+e.1.nextOffset+e.1.width≤capacity)
    (binding : ∀ rho∈sample,(witness rho).tables.map (terminalTableMeaning metadataOf)=meanings)
    (constantBound : ∀ rho∈sample,∀ e∈(witness rho).constants,capacity≤e.1)
    (members : ∀ rho∈sample,∀ t∈(witness rho).tables,metadataOf t∈metadata)
    (placements : ∀ rho∈sample,∀ t∈(witness rho).tables,
      symbolicPlacementMetadataCheck t.compiled.placement (metadataOf t)=true)
    (selectors : ∀ rho∈sample,∀ t∈(witness rho).tables,
      symbolicSelectorCheck (metadataOf t).rowLog t.compiled.placement (gkrTableHistoryPoint (metadataOf t) history)=true)
    (widths : ∀ rho∈sample,∀ t∈(witness rho).tables,t.width≤(metadataOf t).sourceWidth+(metadataOf t).auxiliaryWidth)
    (checked : ∀ rho∈sample,terminalCompilerWitnessCheck capacity rho (witness rho)=true) :
    count sample (fun rho => recoveredWitnessValue C entries layout history (witness rho)=0)≤meanings.length-1 := by
  have bound := terminal_circuit_cancellation_count (terminalMeaningOutputs decoded history meanings)
    lane positive wrong sample distinct (fun rho => recoveredWitnessValue C entries layout history (witness rho)) (by
      intro rho hr
      exact checked_semantic_circuit_value C capacity metadata entries decoded agreement layout history rho (witness rho)
        metadataOf meanings (binding rho hr) geometry (constantBound rho hr) (members rho hr)
        (placements rho hr) (selectors rho hr) (widths rho hr) (checked rho hr))
  simpa only [terminalMeaningOutputs,List.length_map] using bound

end NearCompression
