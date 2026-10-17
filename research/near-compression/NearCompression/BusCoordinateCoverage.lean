import NearCompression.BoundedBusCoordinateTyping
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra

theorem bus_formula_sum_column_bound (xs : List (BusProgramFormula Fp8)) (width : Nat)
    (bounds : ∀ e∈xs,busFormulaColumnBound e≤width) :
    busFormulaColumnBound (busFormulaSum xs)≤width := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    exact Nat.max_le.mpr ⟨bounds x (by simp),ih (fun e he=>bounds e (by simp [he]))⟩

/-- Logical auxiliary width a requires exactly 8*a physical coordinate
columns after the source prefix, including next-row accesses. -/
theorem bus_coordinate_column_coverage (width auxiliaries column : Nat) (next : Bool)
    (bound : column<width+auxiliaries) :
    busFormulaColumnBound (busCoordinateColumnFormula width column next)≤width+8*auxiliaries := by
  by_cases hc : column<width
  · cases next <;> simp only [busCoordinateColumnFormula,hc,ite_true,Bool.false_eq_true,ite_false,busFormulaColumnBound] <;> omega
  · simp only [busCoordinateColumnFormula,hc,ite_false]
    apply bus_formula_sum_column_bound
    intro e he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
    have ib := List.mem_range.mp hi
    cases next <;> simp only [Bool.false_eq_true,ite_false,ite_true,busFormulaColumnBound] <;> omega

theorem bus_coordinate_formula_coverage (width auxiliaries : Nat) (e : BusProgramFormula Fp8)
    (bound : busFormulaColumnBound e≤width+auxiliaries) :
    busFormulaColumnBound (lowerBusCoordinates width e)≤width+8*auxiliaries := by
  induction e with
  | literal x | first | last | transition => exact Nat.zero_le _
  | current c => exact bus_coordinate_column_coverage width auxiliaries c false (by change c+1≤_ at bound;omega)
  | next c => exact bus_coordinate_column_coverage width auxiliaries c true (by change c+1≤_ at bound;omega)
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    exact Nat.max_le.mpr ⟨ha (Nat.le_trans (Nat.le_max_left _ _) bound),hb (Nat.le_trans (Nat.le_max_right _ _) bound)⟩

/-- Zipped provenance suffices for base descent of any recovered lane,
including auxiliaries. No distinct-lane or externally selected index premise. -/
theorem typed_joint_zip_recovered_base
    (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout) (geometry : CanonicalLaneSelectors layout metadata)
    (domain : List Fp8) (distinct : domain.Nodup) (basePoints : ∀ x∈domain,Fp8.IsBase x)
    (D T : Nat) (threshold : T≤domain.length) (enough : D≤T)
    (sources : List (Fp8 → Fp)) (polys : List (Poly Fp8)) (sourceShape : sources.length=metadata.length)
    (representative : JointBetaRepresentative domain (fun _=>1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) (fp8TypedSourceOracles sources) polys)
    (lane : GKRSourceLane) (polynomial : Poly Fp8) (member : (lane,polynomial)∈metadata.zip polys)
    (offset row : Nat) : Fp8.IsBase (recoveredColumnValues layout.commonLog lane offset polynomial row) := by
  obtain ⟨i,hi,same⟩ := List.mem_iff_getElem.mp member
  have shape : polys.length=metadata.length := by
    simpa only [fp8TypedSourceOracles,List.length_map,sourceShape] using representative.1
  have il : i<metadata.length := by simpa only [List.length_zip,shape,Nat.min_self] using hi
  have left := congrArg Prod.fst same
  have right := congrArg Prod.snd same
  simp only [List.getElem_zip] at left right
  rw [←left,←right]
  exact fp8_typed_joint_recovered_base layout metadata valid geometry domain distinct basePoints
    D T threshold enough sources polys sourceShape representative i il offset row

/-- Precompiler decoded-column provenance plus the derived coordinate width
is enough to transport a logical auxiliary formula to the decoded table. -/
theorem metadata_typed_coordinate_formula
    (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout) (geometry : CanonicalLaneSelectors layout metadata)
    (domain : List Fp8) (distinct : domain.Nodup) (basePoints : ∀ x∈domain,Fp8.IsBase x)
    (D T : Nat) (threshold : T≤domain.length) (enough : D≤T)
    (sources : List (Fp8 → Fp)) (polys : List (Poly Fp8)) (sourceShape : sources.length=metadata.length)
    (representative : JointBetaRepresentative domain (fun _=>1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) (fp8TypedSourceOracles sources) polys)
    (table : GKRTableMetadata) (auxiliaries : Nat) (auxWidth : table.auxiliaryWidth=8*auxiliaries)
    (decoded : Nat → Nat → Fp8)
    (provenance : ∀ c,c<table.sourceWidth+table.auxiliaryWidth → ∃ polynomial : Poly Fp8,
      (metadataColumnLane table c,polynomial)∈metadata.zip polys ∧
      decoded c=recoveredColumnValues layout.commonLog (metadataColumnLane table c) (metadataColumnOffset table c) polynomial)
    (row : Nat) (e : BusProgramFormula Fp8) (bound : busFormulaColumnBound e≤table.sourceWidth+auxiliaries) :
    let tr := decodedTableTrace table.rowLog decoded
    busProgramFormulaValue (busRowProgramEnv tr 0 row) (lowerBusCoordinates table.sourceWidth e)=
      busProgramFormulaValue (busRowProgramEnv
        (airAuxCoordinateTrace (decodedBaseTrace tr) (fun _=>table.sourceWidth)) 0 row) e := by
  intro tr
  apply decoded_bus_coordinate_lowering_bounded tr (fun _=>table.sourceWidth) 0 row e
  intro r c hc
  have coverage := bus_coordinate_formula_coverage table.sourceWidth auxiliaries e bound
  obtain ⟨polynomial,member,same⟩ := provenance c (by omega)
  change Fp8.IsBase (decoded c r)
  rw [same]
  exact typed_joint_zip_recovered_base layout metadata valid geometry domain distinct basePoints D T threshold enough
    sources polys sourceShape representative _ polynomial member (metadataColumnOffset table c) r

end NearCompression
