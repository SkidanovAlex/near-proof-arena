import NearCompression.DecodedFormulaCircuit
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

/-- A metadata-only placement used to select decoded columns before any
compiler tables, selectors, mixing challenges or batching challenge. -/
def metadataZeroPlacement {K : Type} [Field K] (table : GKRTableMetadata) : TerminalSymbolicPlacement K :=
  ⟨table.blockOffset,table.columnCapacity,0,0,0⟩

/-- One decoded table is valid for all later placements that match its slot
metadata. Selector values may vary: each environment uses its own selectors. -/
theorem decoded_table_before_placement {K : Type} [Field K]
    (C : Nat) (metadata : List GKRTableMetadata) (entries : List (GKRSourceLane × Poly K))
    (canonical : entries.map Prod.fst=metadata.flatMap gkrMetadataLanes)
    (disjoint : AllLaneSupportsDisjoint (entries.map Prod.fst))
    (table : GKRTableMetadata) (member : table∈metadata) :
    ∃ decoded : Nat → Nat → K,
      (∀ column,column<table.sourceWidth+table.auxiliaryWidth →
        ∃ polynomial : Poly K,(metadataColumnLane table column,polynomial)∈entries ∧
          decoded column=recoveredColumnValues C (metadataColumnLane table column)
            (metadataColumnOffset table column) polynomial) ∧
      ∀ placement : TerminalSymbolicPlacement K,symbolicPlacementMetadataCheck placement table=true →
      ∀ rowpoints : GKRSourceLane → Nat → K,
        TerminalEnvironmentAgreement (table.sourceWidth+table.auxiliaryWidth)
          (placement.environment (gkrScatter (recoveredPrivateSlots C entries rowpoints)))
          (decodedColumnEnvironment table placement decoded rowpoints) := by
  have zeroPlaced : symbolicPlacementMetadataCheck (metadataZeroPlacement (K:=K) table) table=true := by
    simp [symbolicPlacementMetadataCheck,metadataZeroPlacement]
  obtain ⟨decoded,provenance,agreement⟩ := recovered_decoded_environment_agreement C metadata entries canonical disjoint
    table member (metadataZeroPlacement table) zeroPlaced
  refine ⟨decoded,provenance,?_⟩
  intro placement placed rowpoints
  have h := agreement rowpoints
  simp only [symbolicPlacementMetadataCheck,decide_eq_true_eq] at placed
  refine ⟨?_,?_,rfl,rfl,rfl⟩
  · intro c hc
    simpa only [TerminalSymbolicPlacement.environment,metadataZeroPlacement,decodedColumnEnvironment,placed.1] using h.current c hc
  · intro c hc
    simpa only [TerminalSymbolicPlacement.environment,metadataZeroPlacement,decodedColumnEnvironment,placed.1,placed.2] using h.next c hc

/-- The whole family is chosen solely from source tuple and metadata, before
all compiler/selector/rowpoint choices. There is no rho parameter here. -/
theorem decoded_family_before_compiler {K : Type} [Field K]
    (C : Nat) (metadata : List GKRTableMetadata) (entries : List (GKRSourceLane × Poly K))
    (canonical : entries.map Prod.fst=metadata.flatMap gkrMetadataLanes)
    (disjoint : AllLaneSupportsDisjoint (entries.map Prod.fst)) :
    ∃ decoded : GKRTableMetadata → Nat → Nat → K,
      ∀ table∈metadata,
      (∀ column,column<table.sourceWidth+table.auxiliaryWidth →
        ∃ polynomial : Poly K,(metadataColumnLane table column,polynomial)∈entries ∧
          decoded table column=recoveredColumnValues C (metadataColumnLane table column)
            (metadataColumnOffset table column) polynomial) ∧
      ∀ placement : TerminalSymbolicPlacement K,symbolicPlacementMetadataCheck placement table=true →
      ∀ rowpoints : GKRSourceLane → Nat → K,
        TerminalEnvironmentAgreement (table.sourceWidth+table.auxiliaryWidth)
          (placement.environment (gkrScatter (recoveredPrivateSlots C entries rowpoints)))
          (decodedColumnEnvironment table placement (decoded table) rowpoints) := by
  classical
  have each (table : GKRTableMetadata) : ∃ decoded : Nat → Nat → K,table∈metadata →
      (∀ column,column<table.sourceWidth+table.auxiliaryWidth →
        ∃ polynomial : Poly K,(metadataColumnLane table column,polynomial)∈entries ∧
          decoded column=recoveredColumnValues C (metadataColumnLane table column)
            (metadataColumnOffset table column) polynomial) ∧
      ∀ placement : TerminalSymbolicPlacement K,symbolicPlacementMetadataCheck placement table=true →
      ∀ rowpoints : GKRSourceLane → Nat → K,
        TerminalEnvironmentAgreement (table.sourceWidth+table.auxiliaryWidth)
          (placement.environment (gkrScatter (recoveredPrivateSlots C entries rowpoints)))
          (decodedColumnEnvironment table placement decoded rowpoints) := by
    by_cases member : table∈metadata
    · obtain ⟨decoded,provenance,agreement⟩ := decoded_table_before_placement C metadata entries canonical disjoint table member
      exact ⟨decoded,fun _ => ⟨provenance,agreement⟩⟩
    · exact ⟨fun _ _ => 0,fun h => False.elim (member h)⟩
  exact ⟨fun table => Classical.choose (each table),fun table member => Classical.choose_spec (each table) member⟩

/-- Later checked formulas can be transported using this preselected family,
without selecting a new decoded assignment for each batch challenge. -/
theorem preselected_decoded_mixture {K : Type} [Field K] [DecidableEq K]
    (C : Nat) (entries : List (GKRSourceLane × Poly K)) (table : GKRTableMetadata)
    (decoded : Nat → Nat → K)
    (agreement : ∀ placement : TerminalSymbolicPlacement K,symbolicPlacementMetadataCheck placement table=true →
      ∀ rowpoints : GKRSourceLane → Nat → K,
        TerminalEnvironmentAgreement (table.sourceWidth+table.auxiliaryWidth)
          (placement.environment (gkrScatter (recoveredPrivateSlots C entries rowpoints)))
          (decodedColumnEnvironment table placement decoded rowpoints))
    (placement : TerminalSymbolicPlacement K) (placed : symbolicPlacementMetadataCheck placement table=true)
    (rowpoints : GKRSourceLane → Nat → K) (program : List (TerminalInstruction K))
    (publicValues : List K) (width : Nat) (mixing power : K) (residuals : List (AIRBusResidual K × Nat))
    (widthBound : width≤table.sourceWidth+table.auxiliaryWidth)
    (checked : residuals.all (fun r => airBusResidualCheck program publicValues width r.1 r.2)=true) :
    airBusMixValue (placement.environment (gkrScatter (recoveredPrivateSlots C entries rowpoints))) publicValues mixing power residuals=
      airBusMixValue (decodedColumnEnvironment table placement decoded rowpoints) publicValues mixing power residuals := by
  have full := agreement placement placed rowpoints
  have narrow : TerminalEnvironmentAgreement width _ _ :=
    ⟨(fun c hc => full.current c (by omega)),(fun c hc => full.next c (by omega)),full.first,full.last,full.transition⟩
  exact mixed_sum_environment_transport program publicValues width _ _ narrow mixing power residuals checked

/-- All table outputs use the preselected metadata family. This identity can
be substituted into symbolic_formula_recovered_value for each later compiler
certificate, including a rho-dependent circuit, without changing decoded data. -/
theorem preselected_formula_outputs {K : Type} [Field K] [DecidableEq K]
    (C : Nat) (metadata : List GKRTableMetadata) (entries : List (GKRSourceLane × Poly K))
    (decoded : GKRTableMetadata → Nat → Nat → K)
    (agreement : ∀ table∈metadata,∀ placement : TerminalSymbolicPlacement K,
      symbolicPlacementMetadataCheck placement table=true → ∀ rowpoints : GKRSourceLane → Nat → K,
        TerminalEnvironmentAgreement (table.sourceWidth+table.auxiliaryWidth)
          (placement.environment (gkrScatter (recoveredPrivateSlots C entries rowpoints)))
          (decodedColumnEnvironment table placement (decoded table) rowpoints))
    (rowpoints : GKRSourceLane → Nat → K) (tables : List (SymbolicFormulaTable K))
    (metadataOf : SymbolicFormulaTable K → GKRTableMetadata)
    (members : ∀ t∈tables,metadataOf t∈metadata)
    (placements : ∀ t∈tables,symbolicPlacementMetadataCheck t.compiled.placement (metadataOf t)=true)
    (widths : ∀ t∈tables,t.width≤(metadataOf t).sourceWidth+(metadataOf t).auxiliaryWidth)
    (checked : tables.all symbolicFormulaTableCheck=true) :
    symbolicFormulaOutputs (gkrScatter (recoveredPrivateSlots C entries rowpoints)) tables=
      decodedFormulaOutputs metadataOf (fun t => decoded (metadataOf t)) rowpoints tables := by
  unfold symbolicFormulaOutputs decodedFormulaOutputs
  apply List.map_congr_left
  intro t ht
  have checks := List.all_eq_true.mp checked t ht
  simp only [symbolicFormulaTableCheck,Bool.and_eq_true] at checks
  rw [preselected_decoded_mixture C entries (metadataOf t) (decoded (metadataOf t))
    (agreement (metadataOf t) (members t ht)) t.compiled.placement (placements t ht) rowpoints
    t.compiled.program t.publicValues t.width t.mixing 1 t.residuals (widths t ht) checks.1]

end NearCompression
