import NearCompression.GKRPrivateOwnership
import NearCompression.GKRCanonicalCoverage
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Every original compiler table column has ONE decoded polynomial owner
selected from the fixed tuple BEFORE all rowpoint/current-next choices.
Coverage and all-support nonoverlap are both used, not an assumed vector
agreement. This gives an assignment, not a proof that it satisfies the AIR. -/
theorem canonical_column_decoded_owner (C : Nat) (tables : List GKRTableMetadata)
    (entries : List (GKRSourceLane × Poly K))
    (canonical : entries.map Prod.fst=tables.flatMap gkrMetadataLanes)
    (disjoint : AllLaneSupportsDisjoint (entries.map Prod.fst))
    (table : GKRTableMetadata) (tableMember : table∈tables) (auxiliary : Bool)
    (column : Nat) (bound : column<(if auxiliary then table.auxiliaryWidth else table.sourceWidth)) :
    let packing := 2^(if auxiliary then table.auxiliaryPackingLog else table.sourcePackingLog)
    let lane := gkrMetadataLane table auxiliary (column/packing)
    ∃ polynomial : Poly K,(lane,polynomial)∈entries ∧
      ∀ rowpoints : GKRSourceLane → Nat → K,∀ next : Bool,
      let recovered := recoverProjectedPolynomial (2^(C-(lane.rowLog+lane.packingLog)))
        (2^(lane.rowLog+lane.packingLog)) polynomial
      let decoded := recoveredGKRTable lane.rowLog lane.packingLog recovered
      gkrScatter (recoveredPrivateSlots C entries rowpoints)
        (table.blockOffset+(if auxiliary then table.sourceWidth else 0)+
          (if next then table.columnCapacity else 0)+column)=
        if next then genericRowNextMLE lane.rowLog (fun row => decoded row (column%packing)) (rowpoints lane)
        else genericRowMLE lane.rowLog (fun row => decoded row (column%packing)) (rowpoints lane) := by
  dsimp only
  let packing := 2^(if auxiliary then table.auxiliaryPackingLog else table.sourcePackingLog)
  let lane := gkrMetadataLane table auxiliary (column/packing)
  have coverage := metadata_column_coverage table auxiliary false column bound
  change lane∈gkrMetadataLanes table ∧ column%packing<packing ∧
    lane.group*packing+column%packing=column ∧ _ at coverage
  have member : lane∈entries.map Prod.fst := by
    rw [canonical]
    exact List.mem_flatMap.mpr ⟨table,tableMember,coverage.1⟩
  obtain ⟨entry,he,eq⟩ := List.mem_map.mp member
  obtain ⟨actualLane,polynomial⟩ := entry
  change actualLane=lane at eq
  subst actualLane
  refine ⟨polynomial,he,?_⟩
  intro rowpoints next
  have localBound : column%packing<2^lane.packingLog := coverage.2.1
  have live : lane.group*2^lane.packingLog+column%packing<lane.width := by
    change lane.group*packing+column%packing<(if auxiliary then table.auxiliaryWidth else table.sourceWidth)
    rw [coverage.2.2.1]
    exact bound
  have h := recovered_private_lane_read C entries disjoint rowpoints (lane,polynomial) he
    (column%packing) localBound live next
  have index : lane.inputStart+(if next then lane.nextOffset else 0)+lane.group*2^lane.packingLog+column%packing=
      table.blockOffset+(if auxiliary then table.sourceWidth else 0)+
        (if next then table.columnCapacity else 0)+column := by
    have e := coverage.2.2.1
    change lane.group*2^lane.packingLog+column%packing=column at e
    dsimp only [lane,gkrMetadataLane] at e ⊢
    omega
  dsimp only at h
  rw [index] at h
  exact h
end NearCompression
