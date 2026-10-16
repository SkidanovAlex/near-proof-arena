import NearCompression.SymbolicFormulaCheck
import NearCompression.GKRCanonicalAssignment
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

def metadataColumnLane (table : GKRTableMetadata) (column : Nat) : GKRSourceLane :=
  if column<table.sourceWidth then gkrMetadataLane table false (column/2^table.sourcePackingLog)
  else gkrMetadataLane table true ((column-table.sourceWidth)/2^table.auxiliaryPackingLog)

def metadataColumnOffset (table : GKRTableMetadata) (column : Nat) : Nat :=
  if column<table.sourceWidth then column%2^table.sourcePackingLog
  else (column-table.sourceWidth)%2^table.auxiliaryPackingLog

def recoveredColumnValues {K : Type} [Field K] (C : Nat) (lane : GKRSourceLane)
    (offset : Nat) (polynomial : Poly K) : Nat → K :=
  fun row => recoveredGKRTable lane.rowLog lane.packingLog
    (recoverProjectedPolynomial (2^(C-(lane.rowLog+lane.packingLog)))
      (2^(lane.rowLog+lane.packingLog)) polynomial) row offset

def symbolicPlacementMetadataCheck {K : Type} (placement : TerminalSymbolicPlacement K)
    (table : GKRTableMetadata) : Bool :=
  decide (placement.base=table.blockOffset ∧ placement.nextOffset=table.columnCapacity)

/-- A column's polynomial owner is fixed before choosing rowpoints or whether
to read current/next. Source and auxiliary columns use the actual packed lane. -/
theorem recovered_symbolic_column_owner {K : Type} [Field K]
    (C : Nat) (metadata : List GKRTableMetadata) (entries : List (GKRSourceLane × Poly K))
    (canonical : entries.map Prod.fst=metadata.flatMap gkrMetadataLanes)
    (disjoint : AllLaneSupportsDisjoint (entries.map Prod.fst))
    (table : GKRTableMetadata) (member : table∈metadata)
    (placement : TerminalSymbolicPlacement K)
    (placed : symbolicPlacementMetadataCheck placement table=true)
    (column : Nat) (bound : column<table.sourceWidth+table.auxiliaryWidth) :
    ∃ polynomial : Poly K,(metadataColumnLane table column,polynomial)∈entries ∧
      ∀ rowpoints : GKRSourceLane → Nat → K,∀ next : Bool,
      let env := placement.environment (gkrScatter (recoveredPrivateSlots C entries rowpoints))
      (if next then env.next column else env.current column)=
        if next then genericRowNextMLE table.rowLog
          (recoveredColumnValues C (metadataColumnLane table column) (metadataColumnOffset table column) polynomial)
          (rowpoints (metadataColumnLane table column))
        else genericRowMLE table.rowLog
          (recoveredColumnValues C (metadataColumnLane table column) (metadataColumnOffset table column) polynomial)
          (rowpoints (metadataColumnLane table column)) := by
  simp only [symbolicPlacementMetadataCheck,decide_eq_true_eq] at placed
  by_cases source : column<table.sourceWidth
  · have h := canonical_column_decoded_owner C metadata entries canonical disjoint table member false column source
    obtain ⟨poly,hp,reads⟩ := h
    refine ⟨poly,?_,?_⟩
    · simpa only [metadataColumnLane,source,ite_true,Bool.false_eq_true,ite_false] using hp
    · intro rowpoints next
      unfold recoveredColumnValues
      have read := reads rowpoints next
      cases next <;>
        simpa only [metadataColumnLane,metadataColumnOffset,source,ite_true,Bool.false_eq_true,ite_false,
          TerminalSymbolicPlacement.environment,placed.1,placed.2,gkrMetadataLane,
          recoveredColumnValues,Nat.add_zero] using read
  · have auxiliary : column-table.sourceWidth<table.auxiliaryWidth := by omega
    have h := canonical_column_decoded_owner C metadata entries canonical disjoint table member true
      (column-table.sourceWidth) auxiliary
    obtain ⟨poly,hp,reads⟩ := h
    refine ⟨poly,?_,?_⟩
    · simpa only [metadataColumnLane,source,ite_false,ite_true] using hp
    · intro rowpoints next
      unfold recoveredColumnValues
      have read := reads rowpoints next
      have currentIndex : table.blockOffset+table.sourceWidth+0+(column-table.sourceWidth)=
          table.blockOffset+column := by omega
      have nextIndex : table.blockOffset+table.sourceWidth+table.columnCapacity+(column-table.sourceWidth)=
          table.blockOffset+table.columnCapacity+column := by omega
      cases next <;>
        simpa only [metadataColumnLane,metadataColumnOffset,source,ite_true,Bool.false_eq_true,ite_false,
          TerminalSymbolicPlacement.environment,placed.1,placed.2,gkrMetadataLane,
          recoveredColumnValues,currentIndex,nextIndex] using read

/-- One entire decoded column table is chosen from the fixed tuple before all
rowpoint/current-next choices. This is environment construction, not trace
validity or commitment extraction. Each live column retains tuple provenance. -/
theorem recovered_symbolic_environment {K : Type} [Field K]
    (C : Nat) (metadata : List GKRTableMetadata) (entries : List (GKRSourceLane × Poly K))
    (canonical : entries.map Prod.fst=metadata.flatMap gkrMetadataLanes)
    (disjoint : AllLaneSupportsDisjoint (entries.map Prod.fst))
    (table : GKRTableMetadata) (member : table∈metadata)
    (placement : TerminalSymbolicPlacement K)
    (placed : symbolicPlacementMetadataCheck placement table=true) :
    ∃ decoded : Nat → Nat → K,
      (∀ column, column<table.sourceWidth+table.auxiliaryWidth →
        ∃ polynomial : Poly K,(metadataColumnLane table column,polynomial)∈entries ∧
          decoded column=recoveredColumnValues C (metadataColumnLane table column) (metadataColumnOffset table column) polynomial) ∧
      ∀ column, column<table.sourceWidth+table.auxiliaryWidth →
        ∀ rowpoints : GKRSourceLane → Nat → K,∀ next : Bool,
        let env := placement.environment (gkrScatter (recoveredPrivateSlots C entries rowpoints))
        (if next then env.next column else env.current column)=
          if next then genericRowNextMLE table.rowLog (decoded column) (rowpoints (metadataColumnLane table column))
          else genericRowMLE table.rowLog (decoded column) (rowpoints (metadataColumnLane table column)) := by
  classical
  have owner := recovered_symbolic_column_owner C metadata entries canonical disjoint table member placement placed
  let polynomial := fun (column : Nat) (h : column<table.sourceWidth+table.auxiliaryWidth) =>
    Classical.choose (owner column h)
  let decoded := fun column => if h : column<table.sourceWidth+table.auxiliaryWidth then
    recoveredColumnValues C (metadataColumnLane table column) (metadataColumnOffset table column) (polynomial column h)
    else fun _ => 0
  refine ⟨decoded,?_,?_⟩
  · intro column bound
    refine ⟨polynomial column bound,(Classical.choose_spec (owner column bound)).1,?_⟩
    simp only [decoded,dite_eq_left bound]
  · intro column bound rowpoints next
    have reads := (Classical.choose_spec (owner column bound)).2 rowpoints next
    simpa only [decoded,dite_eq_left bound,polynomial] using reads

private def environmentSmokeMetadata : GKRTableMetadata :=
  ⟨2,0,4,8,3,2,1,0⟩
private def environmentSmokePlacement : TerminalSymbolicPlacement Rat := ⟨4,8,0,0,0⟩

/-- Source and auxiliary branch offsets differ; current and next read the same
logical column in distinct physical halves. Incorrect placement is rejected. -/
theorem recovered_environment_placement_regressions :
    symbolicPlacementMetadataCheck environmentSmokePlacement environmentSmokeMetadata=true ∧
    symbolicPlacementMetadataCheck {environmentSmokePlacement with base:=5} environmentSmokeMetadata=false ∧
    symbolicPlacementMetadataCheck {environmentSmokePlacement with nextOffset:=7} environmentSmokeMetadata=false ∧
    (metadataColumnLane environmentSmokeMetadata 2).inputStart=4 ∧
    (metadataColumnLane environmentSmokeMetadata 2).group=1 ∧
    metadataColumnOffset environmentSmokeMetadata 2=0 ∧
    (metadataColumnLane environmentSmokeMetadata 3).inputStart=7 ∧
    (metadataColumnLane environmentSmokeMetadata 3).group=0 ∧
    (metadataColumnLane environmentSmokeMetadata 4).group=1 ∧
    (environmentSmokePlacement.environment (fun i => (i:Rat))).current 3=7 ∧
    (environmentSmokePlacement.environment (fun i => (i:Rat))).next 3=15 := by decide +kernel

end NearCompression
