import NearCompression.DecodedSelectorBinding
import NearCompression.GKRHistoryCoordinates
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

/-- Total extraction of a table's row coordinates from chronological history.
Short histories are zero padded; valid history bounds below rule that out. -/
def gkrTableHistoryPoint {K : Type} [Field K] (table : GKRTableMetadata) (history : List K) : List K :=
  (List.range table.rowLog).map (fun i => history.getD (table.rowOffset+i) 0)

theorem gkr_table_history_point_length {K : Type} [Field K]
    (table : GKRTableMetadata) (history : List K) :
    (gkrTableHistoryPoint table history).length=table.rowLog := by
  simp [gkrTableHistoryPoint]

/-- Source and auxiliary packing change column ownership, but not the row
coordinate block. All live columns use exactly the table's history point. -/
theorem gkr_table_history_lane_alignment {K : Type} [Field K]
    (layout : GKRJointLayout) (table : GKRTableMetadata) (history : List K)
    (column i : Nat) (bound : i<table.rowLog) :
    gkrHistoryRowpoints layout history (metadataColumnLane table column) i=
      (gkrTableHistoryPoint table history).getD i 0 := by
  have length : i<(gkrTableHistoryPoint table history).length := by
    rw [gkr_table_history_point_length];exact bound
  have read : (gkrTableHistoryPoint table history).getD i 0=history.getD (table.rowOffset+i) 0 := by
    simp only [List.getD,List.getElem?_eq_getElem length,Option.getD_some]
    simp only [gkrTableHistoryPoint,List.getElem_map,List.getElem_range]
    rfl
  rw [read]
  unfold gkrHistoryRowpoints metadataColumnLane
  split <;> simp only [gkrMetadataLane,gkrPointBlock,bound,ite_true]

/-- With checked metadata and a complete chronological history, extracted
coordinates are actual history entries, rather than default padding. -/
theorem gkr_table_history_point_unpadded {K : Type} [Field K]
    (layout : GKRJointLayout) (table : GKRTableMetadata) (history : List K)
    (checked : gkrTableMetadataCheck layout table=true)
    (length : history.length=gkrHistoryLength layout)
    (i : Nat) (bound : i<table.rowLog) :
    ∃ h : table.rowOffset+i<history.length,
      (gkrTableHistoryPoint table history).getD i 0=history[table.rowOffset+i]'h := by
  simp only [gkrTableMetadataCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
  have rows := checked.1.1.1.1.1
  have size : history.length=layout.rowCoordinates+2*layout.inputLog+1 := length
  have h : table.rowOffset+i<history.length := by omega
  refine ⟨h,?_⟩
  have len : i<(gkrTableHistoryPoint table history).length := by
    rw [gkr_table_history_point_length];exact bound
  simp only [List.getD,List.getElem?_eq_getElem len,Option.getD_some]
  simp only [gkrTableHistoryPoint,List.getElem_map,List.getElem_range,List.getD,
    List.getElem?_eq_getElem h,Option.getD_some]

theorem history_decoded_environment {K : Type} [Field K] [DecidableEq K]
    (layout : GKRJointLayout) (table : GKRTableMetadata) (history : List K)
    (placement : TerminalSymbolicPlacement K) (decoded : Nat → Nat → K)
    (selectors : symbolicSelectorCheck table.rowLog placement (gkrTableHistoryPoint table history)=true) :
    TerminalEnvironmentAgreement (table.sourceWidth+table.auxiliaryWidth)
      (decodedColumnEnvironment table placement decoded (gkrHistoryRowpoints layout history))
      (decodedRowEnvironment table.rowLog decoded (gkrTableHistoryPoint table history)) := by
  apply decoded_common_point_environment table placement decoded _ _ selectors
  intro c _ i hi
  exact gkr_table_history_lane_alignment layout table history c i hi

theorem history_decoded_mixture {K : Type} [Field K] [DecidableEq K]
    (layout : GKRJointLayout) (table : GKRTableMetadata) (history : List K)
    (placement : TerminalSymbolicPlacement K) (decoded : Nat → Nat → K)
    (selectors : symbolicSelectorCheck table.rowLog placement (gkrTableHistoryPoint table history)=true)
    (program : List (TerminalInstruction K)) (publicValues : List K) (width : Nat)
    (mixing power : K) (residuals : List (AIRBusResidual K × Nat))
    (widthBound : width≤table.sourceWidth+table.auxiliaryWidth)
    (checked : residuals.all (fun r => airBusResidualCheck program publicValues width r.1 r.2)=true) :
    airBusMixValue (decodedColumnEnvironment table placement decoded (gkrHistoryRowpoints layout history))
      publicValues mixing power residuals=
    airBusMixValue (decodedRowEnvironment table.rowLog decoded (gkrTableHistoryPoint table history))
      publicValues mixing power residuals := by
  apply decoded_common_point_mixture table placement decoded _ _ selectors _ program publicValues width mixing power residuals widthBound checked
  intro c _ i hi
  exact gkr_table_history_lane_alignment layout table history c i hi

/-- All table outputs now use chronological table points and row-flag MLEs. -/
def historyRowFormulaOutputs {K : Type} [Field K]
    (metadataOf : SymbolicFormulaTable K → GKRTableMetadata)
    (decoded : SymbolicFormulaTable K → Nat → Nat → K)
    (history : List K) (tables : List (SymbolicFormulaTable K)) : List (K × K) :=
  tables.map (fun t =>
    (airBusMixValue (decodedRowEnvironment (metadataOf t).rowLog (decoded t)
      (gkrTableHistoryPoint (metadataOf t) history)) t.publicValues t.mixing 1 t.residuals*
      t.compiled.entry.weight,t.compiled.entry.claim))

theorem history_decoded_formula_outputs {K : Type} [Field K] [DecidableEq K]
    (layout : GKRJointLayout) (history : List K) (tables : List (SymbolicFormulaTable K))
    (metadataOf : SymbolicFormulaTable K → GKRTableMetadata)
    (decoded : SymbolicFormulaTable K → Nat → Nat → K)
    (selectors : ∀ t∈tables,symbolicSelectorCheck (metadataOf t).rowLog t.compiled.placement
      (gkrTableHistoryPoint (metadataOf t) history)=true)
    (widths : ∀ t∈tables,t.width≤(metadataOf t).sourceWidth+(metadataOf t).auxiliaryWidth)
    (checked : tables.all symbolicFormulaTableCheck=true) :
    decodedFormulaOutputs metadataOf decoded (gkrHistoryRowpoints layout history) tables=
      historyRowFormulaOutputs metadataOf decoded history tables := by
  unfold decodedFormulaOutputs historyRowFormulaOutputs
  apply List.map_congr_left
  intro t ht
  have checks := List.all_eq_true.mp checked t ht
  simp only [symbolicFormulaTableCheck,Bool.and_eq_true] at checks
  rw [history_decoded_mixture layout (metadataOf t) history t.compiled.placement (decoded t)
    (selectors t ht) t.compiled.program t.publicValues t.width t.mixing 1 t.residuals (widths t ht) checks.1]

private def historySmokeTable : GKRTableMetadata := ⟨2,1,4,8,3,2,1,0⟩
/-- Offset-sensitive extraction, source/auxiliary agreement, and explicit
short-history padding. This prevents treating total extraction as authentication. -/
theorem history_decoded_regressions :
    gkrTableHistoryPoint historySmokeTable ([99,2,3,88] : List Rat)=[2,3] ∧
    gkrTableHistoryPoint historySmokeTable ([99,2] : List Rat)=[2,0] ∧
    gkrTableHistoryPoint {historySmokeTable with rowOffset:=2} ([99,2,3,88] : List Rat)=[3,88] ∧
    gkrHistoryRowpoints ⟨4,1,3,8⟩ ([99,2,3,88] : List Rat) (metadataColumnLane historySmokeTable 2) 1=3 ∧
    gkrHistoryRowpoints ⟨4,1,3,8⟩ ([99,2,3,88] : List Rat) (metadataColumnLane historySmokeTable 4) 1=3 ∧
    gkrHistoryRowpoints ⟨4,1,3,8⟩ ([99,2,3,88] : List Rat) (metadataColumnLane historySmokeTable 4) 2=0 := by decide +kernel

end NearCompression
