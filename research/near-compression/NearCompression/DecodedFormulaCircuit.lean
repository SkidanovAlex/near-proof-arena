import NearCompression.FormulaEnvironmentTransport
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

/-- Compiler tables are explicitly associated with source metadata. This does
not identify their supplied formulas with the intended AIR specification. -/
def decodedFormulaOutputs {K : Type} [Field K]
    (metadataOf : SymbolicFormulaTable K → GKRTableMetadata)
    (decoded : SymbolicFormulaTable K → Nat → Nat → K)
    (rowpoints : GKRSourceLane → Nat → K) (tables : List (SymbolicFormulaTable K)) : List (K × K) :=
  tables.map (fun t =>
    (airBusMixValue (decodedColumnEnvironment (metadataOf t) t.compiled.placement (decoded t) rowpoints)
      t.publicValues t.mixing 1 t.residuals*t.compiled.entry.weight,t.compiled.entry.claim))

/-- One family of decoded tables, chosen from the fixed polynomial tuple before
all rowpoints, supplies every checked formula table's output. -/
theorem decoded_formula_outputs {K : Type} [Field K] [DecidableEq K]
    (C : Nat) (metadata : List GKRTableMetadata) (entries : List (GKRSourceLane × Poly K))
    (canonical : entries.map Prod.fst=metadata.flatMap gkrMetadataLanes)
    (disjoint : AllLaneSupportsDisjoint (entries.map Prod.fst))
    (tables : List (SymbolicFormulaTable K)) (metadataOf : SymbolicFormulaTable K → GKRTableMetadata)
    (members : ∀ t∈tables,metadataOf t∈metadata)
    (placements : ∀ t∈tables,symbolicPlacementMetadataCheck t.compiled.placement (metadataOf t)=true)
    (widths : ∀ t∈tables,t.width≤(metadataOf t).sourceWidth+(metadataOf t).auxiliaryWidth)
    (checks : tables.all symbolicFormulaTableCheck=true) :
    ∃ decoded : SymbolicFormulaTable K → Nat → Nat → K,
      (∀ t∈tables,∀ column,column<(metadataOf t).sourceWidth+(metadataOf t).auxiliaryWidth →
        ∃ polynomial : Poly K,(metadataColumnLane (metadataOf t) column,polynomial)∈entries ∧
          decoded t column=recoveredColumnValues C (metadataColumnLane (metadataOf t) column)
            (metadataColumnOffset (metadataOf t) column) polynomial) ∧
      ∀ rowpoints : GKRSourceLane → Nat → K,
        symbolicFormulaOutputs (gkrScatter (recoveredPrivateSlots C entries rowpoints)) tables=
        decodedFormulaOutputs metadataOf decoded rowpoints tables := by
  classical
  have each (t : SymbolicFormulaTable K) : ∃ d : Nat → Nat → K, t∈tables →
      (∀ column,column<(metadataOf t).sourceWidth+(metadataOf t).auxiliaryWidth →
        ∃ polynomial : Poly K,(metadataColumnLane (metadataOf t) column,polynomial)∈entries ∧
          d column=recoveredColumnValues C (metadataColumnLane (metadataOf t) column)
            (metadataColumnOffset (metadataOf t) column) polynomial) ∧
      ∀ rowpoints : GKRSourceLane → Nat → K,
        airBusMixValue (t.compiled.placement.environment (gkrScatter (recoveredPrivateSlots C entries rowpoints)))
          t.publicValues t.mixing 1 t.residuals=
        airBusMixValue (decodedColumnEnvironment (metadataOf t) t.compiled.placement d rowpoints)
          t.publicValues t.mixing 1 t.residuals := by
    by_cases ht : t∈tables
    · obtain ⟨d,provenance,transport⟩ := recovered_mixed_formula_transport C metadata entries canonical disjoint
        (metadataOf t) (members t ht) t.compiled.placement (placements t ht)
      refine ⟨d,fun _ => ⟨provenance,?_⟩⟩
      intro rowpoints
      have checked := List.all_eq_true.mp checks t ht
      simp only [symbolicFormulaTableCheck,Bool.and_eq_true] at checked
      exact transport rowpoints t.compiled.program t.publicValues t.width t.mixing 1 t.residuals (widths t ht) checked.1
    · exact ⟨fun _ _ => 0,fun h => False.elim (ht h)⟩
  let decoded := fun t => Classical.choose (each t)
  have spec := fun t => Classical.choose_spec (each t)
  refine ⟨decoded,?_,?_⟩
  · intro t ht
    exact (spec t ht).1
  · intro rowpoints
    unfold symbolicFormulaOutputs decodedFormulaOutputs
    apply List.map_congr_left
    intro t ht
    rw [(spec t ht).2 rowpoints]

/-- Compose checked finite-circuit execution with the decoded table family.
No pointwise circuit assignment equality is assumed. This is an exact identity,
not yet an acceptance-to-valid-execution or computational soundness theorem. -/
theorem decoded_formula_recovered_circuit {K : Type} [Field K] [DecidableEq K]
    (C capacity : Nat) (metadata : List GKRTableMetadata) (entries : List (GKRSourceLane × Poly K))
    (canonical : entries.map Prod.fst=metadata.flatMap gkrMetadataLanes)
    (disjoint : AllLaneSupportsDisjoint (entries.map Prod.fst))
    (constants : List (Nat × K))
    (geometry : ∀ e∈entries,e.1.inputStart+e.1.width≤capacity ∧ e.1.inputStart+e.1.nextOffset+e.1.width≤capacity)
    (constantBound : ∀ e∈constants,capacity≤e.1)
    (nodes : List (TerminalDAGNode K)) (rho : K) (tables : List (SymbolicFormulaTable K))
    (metadataOf : SymbolicFormulaTable K → GKRTableMetadata)
    (members : ∀ t∈tables,metadataOf t∈metadata)
    (placements : ∀ t∈tables,symbolicPlacementMetadataCheck t.compiled.placement (metadataOf t)=true)
    (widths : ∀ t∈tables,t.width≤(metadataOf t).sourceWidth+(metadataOf t).auxiliaryWidth)
    (balance : TerminalBalanceCertificate K) (root zeroNode : Nat)
    (live positions : List Nat) (zeroSlot : Nat) (stages : List TerminalStoredPlan) (outputSlot : Nat)
    (checked : symbolicFormulaCompilerCheck nodes (gkrScatter constants) rho tables balance root zeroNode capacity
      live positions zeroSlot stages outputSlot=true) :
    ∃ decoded : SymbolicFormulaTable K → Nat → Nat → K,
      (∀ t∈tables,∀ column,column<(metadataOf t).sourceWidth+(metadataOf t).auxiliaryWidth →
        ∃ polynomial : Poly K,(metadataColumnLane (metadataOf t) column,polynomial)∈entries ∧
          decoded t column=recoveredColumnValues C (metadataColumnLane (metadataOf t) column)
            (metadataColumnOffset (metadataOf t) column) polynomial) ∧
      ∀ rowpoints : GKRSourceLane → Nat → K,
        gkrFiniteCircuit (gkrRecoveredCircuitInput C entries rowpoints constants)
          (stages.map (fun s => s.gates)) outputSlot=
        terminalResidualValue rho 1 (decodedFormulaOutputs metadataOf decoded rowpoints tables) := by
  have tableChecks := checked
  simp only [symbolicFormulaCompilerCheck,Bool.and_eq_true] at tableChecks
  obtain ⟨decoded,provenance,outputs⟩ := decoded_formula_outputs C metadata entries canonical disjoint
    tables metadataOf members placements widths tableChecks.2
  refine ⟨decoded,provenance,?_⟩
  intro rowpoints
  rw [symbolic_formula_recovered_value C capacity entries rowpoints constants geometry constantBound
    nodes rho tables balance root zeroNode live positions zeroSlot stages outputSlot checked,
    outputs rowpoints]

end NearCompression
