import NearCompression.BusCoordinateFormulaLowering
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra

/-- Exclusive bound on columns read by a formula; selectors read no columns. -/
def busFormulaColumnBound {K : Type} : BusProgramFormula K → Nat
  | .literal _ | .first | .last | .transition => 0
  | .current c | .next c => c+1
  | .add a b | .sub a b | .mul a b => max (busFormulaColumnBound a) (busFormulaColumnBound b)

/-- Base descent is needed only for cells read by the formula. Cyclic next
reads use the same bounded columns, at the next row. -/
theorem bus_formula_bounded_base_projection (tr : Trace Fp8) (t row : Nat)
    (e : BusProgramFormula Fp8)
    (base : ∀ r c,c<busFormulaColumnBound e → Fp8.IsBase (tr.cell t r c)) :
    busProgramFormulaValue (busRowProgramEnv tr t row) e=
      busProgramFormulaValue (busRowProgramEnv (airExt8Trace (decodedBaseTrace tr)) t row) e := by
  induction e with
  | literal x | first | last | transition => rfl
  | current c =>
    exact (decoded_base_trace_cell tr t row c (base row c (by simp [busFormulaColumnBound]))).symm
  | next c =>
    exact (decoded_base_trace_cell tr t ((row+1)%tr.height t) c
      (base _ c (by simp [busFormulaColumnBound]))).symm
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    have ba : ∀ r c,c<busFormulaColumnBound a → Fp8.IsBase (tr.cell t r c) :=
      fun r c hc=>base r c (Nat.lt_of_lt_of_le hc (Nat.le_max_left _ _))
    have bb : ∀ r c,c<busFormulaColumnBound b → Fp8.IsBase (tr.cell t r c) :=
      fun r c hc=>base r c (Nat.lt_of_lt_of_le hc (Nat.le_max_right _ _))
    simp only [busProgramFormulaValue,ha ba,hb bb]

/-- No premise is imposed on unreferenced columns or other tables. -/
theorem decoded_bus_coordinate_lowering_bounded (tr : Trace Fp8) (sourceWidth : Nat → Nat)
    (t row : Nat) (e : BusProgramFormula Fp8)
    (base : ∀ r c,c<busFormulaColumnBound (lowerBusCoordinates (sourceWidth t) e) →
      Fp8.IsBase (tr.cell t r c)) :
    busProgramFormulaValue (busRowProgramEnv tr t row) (lowerBusCoordinates (sourceWidth t) e)=
      busProgramFormulaValue (busRowProgramEnv (airAuxCoordinateTrace (decodedBaseTrace tr) sourceWidth) t row) e := by
  rw [bus_formula_bounded_base_projection tr t row _ base]
  exact bus_coordinate_lowering_row_value (decodedBaseTrace tr) sourceWidth t row e

/-- Typed joint PCS representatives discharge the bounded coordinate typing
premise for source AND auxiliary coordinate lanes. Native authentication and
coverage/provenance of those read columns remain explicit. -/
theorem typed_joint_bus_coordinate_lowering
    (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout) (geometry : CanonicalLaneSelectors layout metadata)
    (domain : List Fp8) (distinct : domain.Nodup) (basePoints : ∀ x∈domain,Fp8.IsBase x)
    (D T : Nat) (threshold : T≤domain.length) (enough : D≤T)
    (sources : List (Fp8 → Fp)) (polys : List (Poly Fp8)) (sourceShape : sources.length=metadata.length)
    (representative : JointBetaRepresentative domain (fun _=>1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) (fp8TypedSourceOracles sources) polys)
    (tr : Trace Fp8) (sourceWidth : Nat → Nat) (t row : Nat) (e : BusProgramFormula Fp8)
    (provenance : ∀ r c,c<busFormulaColumnBound (lowerBusCoordinates (sourceWidth t) e) →
      ∃ i,∃ hi : i<metadata.length,∃ offset,
        tr.cell t r c=recoveredColumnValues layout.commonLog metadata[i] offset (polys.getD i Poly.zero) r) :
    busProgramFormulaValue (busRowProgramEnv tr t row) (lowerBusCoordinates (sourceWidth t) e)=
      busProgramFormulaValue (busRowProgramEnv (airAuxCoordinateTrace (decodedBaseTrace tr) sourceWidth) t row) e := by
  apply decoded_bus_coordinate_lowering_bounded tr sourceWidth t row e
  intro r c hc
  obtain ⟨i,hi,offset,same⟩ := provenance r c hc
  rw [same]
  have shape : polys.length=metadata.length := by
    have h := representative.1
    simpa only [fp8TypedSourceOracles,List.length_map,sourceShape] using h
  have pi : i<polys.length := by omega
  simp only [List.getD,List.getElem?_eq_getElem pi,Option.getD_some]
  exact fp8_typed_joint_recovered_base layout metadata valid geometry domain distinct basePoints
    D T threshold enough sources polys sourceShape representative i hi offset r

/-- A reconstructed bus violation becomes a nonzero residual in the local
formula list on decoded PCS coordinates after the proved coordinate lowering. -/
theorem lowered_auxiliary_failure_index (tr : Trace Fp8) (sourceWidth : Nat → Nat)
    (t row : Nat) (pub : List Fp8) (source : List Expr)
    (auxiliary : List (BusProgramFormula Fp8)) (e : BusProgramFormula Fp8) (member : e∈auxiliary)
    (base : ∀ r c,c<busFormulaColumnBound (lowerBusCoordinates (sourceWidth t) e) →
      Fp8.IsBase (tr.cell t r c))
    (wrong : busProgramFormulaValue
      (busRowProgramEnv (airAuxCoordinateTrace (decodedBaseTrace tr) sourceWidth) t row) e≠0) :
    0<source.length+(auxiliary.map (lowerBusCoordinates (sourceWidth t))).length ∧ ∃ lane,
      (airCombinedRowResiduals tr t pub source (auxiliary.map (lowerBusCoordinates (sourceWidth t))) row).getD lane 0≠0 := by
  apply auxiliary_nonzero_combined_index tr t row pub source _ (lowerBusCoordinates (sourceWidth t) e)
    (List.mem_map.mpr ⟨e,member,rfl⟩)
  rw [decoded_bus_coordinate_lowering_bounded tr sourceWidth t row e base]
  exact wrong

end NearCompression
