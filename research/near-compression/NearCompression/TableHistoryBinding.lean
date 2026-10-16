import NearCompression.TwoTableLocalCoordinates
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

/-- Metadata selects the actual table path inside an assembled history.
Trailing GKR/PCS coordinates cannot change that path. -/
theorem table_history_segment {K : Type} [Field K]
    (table : GKRTableMetadata) (earlier point suffix : List K)
    (offset : table.rowOffset=earlier.length) (width : table.rowLog=point.length) :
    gkrTableHistoryPoint table ((earlier++point)++suffix)=point := by
  apply List.ext_getElem
  · simp [gkr_table_history_point_length,width]
  · intro i hi hj
    have bound : i<point.length := hj
    have inside : earlier.length+i<(earlier++point).length := by simp;omega
    simp only [gkrTableHistoryPoint,List.getElem_map,List.getElem_range,offset,List.getD,
      List.getElem?_append_left inside,List.getElem?_append_right (by omega : earlier.length≤earlier.length+i),
      Nat.add_sub_cancel_left,List.getElem?_eq_getElem bound,Option.getD_some]

/-- The two-table take/drop partition coincides with checked row offsets,
even with an arbitrary final-block/PCS suffix appended. -/
theorem two_table_history_points {K : Type} [Field K]
    (first second : GKRTableMetadata) (rows suffix : List K)
    (firstOffset : first.rowOffset=0) (secondOffset : second.rowOffset=first.rowLog)
    (length : rows.length=first.rowLog+second.rowLog) :
    gkrTableHistoryPoint first (rows++suffix)=rows.take first.rowLog ∧
    gkrTableHistoryPoint second (rows++suffix)=rows.drop first.rowLog := by
  have firstLength : (rows.take first.rowLog).length=first.rowLog := by
    simp only [List.length_take];omega
  have secondLength : (rows.drop first.rowLog).length=second.rowLog := by
    simp only [List.length_drop];omega
  have split : rows.take first.rowLog++rows.drop first.rowLog=rows := List.take_append_drop _ _
  constructor
  · have h := table_history_segment first [] (rows.take first.rowLog) (rows.drop first.rowLog++suffix)
      firstOffset firstLength.symm
    simpa only [List.nil_append,←List.append_assoc,split] using h
  · have h := table_history_segment second (rows.take first.rowLog) (rows.drop first.rowLog) suffix
      (secondOffset.trans firstLength.symm) secondLength.symm
    simpa only [split] using h

/-- Recovered private inputs depend only on each live lane's row prefix.
This proves whole-function input stability across the final GKR block,
not just stability of the requested opening functional. -/
theorem recovered_input_history_suffix {K : Type} [Field K]
    (layout : GKRJointLayout) (C : Nat) (entries : List (GKRSourceLane × Poly K))
    (rows suffix : List K) (constants : List (Nat × K))
    (length : rows.length=layout.rowCoordinates)
    (bounded : ∀ e∈entries,e.1.rowOffset+e.1.rowLog≤layout.rowCoordinates) :
    gkrRecoveredCircuitInput C entries (gkrHistoryRowpoints layout (rows++suffix)) constants=
      gkrRecoveredCircuitInput C entries (gkrHistoryRowpoints layout rows) constants := by
  have slots : recoveredPrivateSlots C entries (gkrHistoryRowpoints layout (rows++suffix))=
      recoveredPrivateSlots C entries (gkrHistoryRowpoints layout rows) := by
    unfold recoveredPrivateSlots
    simp only [List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro e he
    rw [gkr_joint_history_rows_unchanged layout rows suffix e.1 length (bounded e he)]
  unfold gkrRecoveredCircuitInput
  rw [slots]

/-- Supply the whole-function input binding required by the concrete GKR/PCS
failure theorem. Constants may depend on rows, but the PCS family must use
that same list after the final block is sampled. -/
theorem concrete_pcs_recovered_input_binding {K : Type} [Field K]
    (sample : List K) (layout : GKRJointLayout) (queries : Nat)
    (entries : List (GKRSourceLane × Poly K)) (constants : List K → List (Nat × K))
    (family : GKRBlockPCSFamily K)
    (bounded : ∀ e∈entries,e.1.rowOffset+e.1.rowLog≤layout.rowCoordinates)
    (constantBinding : ∀ item∈gkrConcretePCSSamples sample layout queries,
      family.constants item.1 item.2.1=constants item.1) :
    ∀ item∈gkrConcretePCSSamples sample layout queries,
      gkrRecoveredCircuitInput layout.commonLog entries (gkrHistoryRowpoints layout item.1) (constants item.1)=
      gkrRecoveredCircuitInput layout.commonLog entries
        (gkrHistoryRowpoints layout (item.1++gkrBlockCoordinates item.2.1)) (family.constants item.1 item.2.1) := by
  intro item member
  rw [constantBinding item member]
  exact (recovered_input_history_suffix layout layout.commonLog entries item.1 (gkrBlockCoordinates item.2.1)
    (constants item.1) (concrete_pcs_sample_lengths sample layout queries item member).1 bounded).symm

end NearCompression
