import NearCompression.FixedJointSourceTrace
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ZkFormal.Air

/-- A live lane cannot occur at two indices under all-slot disjointness.
Empty-support lanes are not incorrectly declared unique. -/
theorem live_lane_index_unique (lanes : List GKRSourceLane) (disjoint : AllLaneSupportsDisjoint lanes)
    (i j : Nat) (hi : i<lanes.length) (hj : j<lanes.length)
    (same : lanes[i]=lanes[j]) (slot : Nat) (live : lanes[i].LiveSlot false slot) : i=j := by
  by_cases equal : i=j
  · exact equal
  · have other : lanes[j].LiveSlot false slot := by rw [←same];exact live
    exact False.elim (disjoint i hi j hj false false (Or.inl equal) slot live other)

/-- Source-column div/mod coverage chooses a unique lane index solely from
metadata, before any representative polynomial tuple or auxiliary choice. -/
theorem metadata_source_column_index (tables : List GKRTableMetadata)
    (disjoint : AllLaneSupportsDisjoint (tables.flatMap gkrMetadataLanes))
    (table : GKRTableMetadata) (member : table∈tables) (column : Nat) (bound : column<table.sourceWidth) :
    ∃ i,∃ hi : i<(tables.flatMap gkrMetadataLanes).length,
      (tables.flatMap gkrMetadataLanes)[i]=metadataColumnLane table column ∧
      ∀ j,∀ hj : j<(tables.flatMap gkrMetadataLanes).length,
        (tables.flatMap gkrMetadataLanes)[j]=metadataColumnLane table column → j=i := by
  have coverage := metadata_column_coverage table false false column bound
  have laneMember : metadataColumnLane table column∈tables.flatMap gkrMetadataLanes := by
    apply List.mem_flatMap.mpr
    refine ⟨table,member,?_⟩
    simpa only [metadataColumnLane,bound,ite_true,Bool.false_eq_true,ite_false] using coverage.1
  obtain ⟨i,hi,same⟩ := List.mem_iff_getElem.mp laneMember
  refine ⟨i,hi,same,?_⟩
  intro j hj other
  have live : (metadataColumnLane table column).LiveSlot false (table.blockOffset+column) := by
    simpa only [metadataColumnLane,bound,ite_true,Bool.false_eq_true,ite_false,Nat.add_zero] using coverage.2.2.2
  apply live_lane_index_unique _ disjoint j i hj hi (other.trans same.symm) (table.blockOffset+column)
  rw [other]
  exact live

/-- Convert existential zip membership into the polynomial at the fixed lane
index. This remains valid without assuming all metadata lanes are distinct. -/
theorem indexed_lane_polynomial {K : Type} (lanes : List GKRSourceLane) (polys : List (Poly K))
    (shape : polys.length=lanes.length) (lane : GKRSourceLane)
    (i : Nat) (hi : i<lanes.length)
    (unique : ∀ j,∀ hj : j<lanes.length,lanes[j]=lane → j=i)
    (p : Poly K) (member : (lane,p)∈lanes.zip polys) :
    p=polys[i]'(by omega) := by
  obtain ⟨j,hj,same⟩ := List.mem_iff_getElem.mp member
  have jl : j<lanes.length := by simpa only [List.length_zip,shape,Nat.min_self] using hj
  have jp : j<polys.length := by omega
  have left := congrArg Prod.fst same
  have right := congrArg Prod.snd same
  simp only [List.getElem_zip] at left right
  have index := unique j jl left
  subst j
  exact right.symm

/-- The preselected decoded-family provenance now becomes the exact indexed
cell equality used by the fixed joint-source trace theorem. -/
theorem decoded_source_indexed_provenance {K : Type} [Field K]
    (C : Nat) (tables : List GKRTableMetadata) (polys : List (Poly K))
    (shape : polys.length=(tables.flatMap gkrMetadataLanes).length)
    (table : GKRTableMetadata) (column : Nat) (decoded : Nat → Nat → K)
    (i : Nat) (hi : i<(tables.flatMap gkrMetadataLanes).length)
    (laneAt : (tables.flatMap gkrMetadataLanes)[i]=metadataColumnLane table column)
    (unique : ∀ j,∀ hj : j<(tables.flatMap gkrMetadataLanes).length,
      (tables.flatMap gkrMetadataLanes)[j]=metadataColumnLane table column → j=i)
    (provenance : ∃ polynomial : Poly K,
      (metadataColumnLane table column,polynomial)∈(tables.flatMap gkrMetadataLanes).zip polys ∧
      decoded column=recoveredColumnValues C (metadataColumnLane table column) (metadataColumnOffset table column) polynomial) :
    ∀ row,decoded column row=recoveredColumnValues C (tables.flatMap gkrMetadataLanes)[i]
      (metadataColumnOffset table column) (polys.getD i Poly.zero) row := by
  obtain ⟨polynomial,member,same⟩ := provenance
  have selected := indexed_lane_polynomial _ polys shape _ i hi unique polynomial member
  intro row
  rw [same,selected,laneAt]
  have pi : i<polys.length := by omega
  simp only [List.getD,List.getElem?_eq_getElem pi,Option.getD_some]

/-- One index family is selected from metadata before any source oracle,
polynomial tuple, decoded trace, or auxiliary strategy is supplied. -/
theorem metadata_source_index_family (tables : List GKRTableMetadata)
    (disjoint : AllLaneSupportsDisjoint (tables.flatMap gkrMetadataLanes))
    (tableAt : Nat → GKRTableMetadata)
    (member : ∀ t,0<(tableAt t).sourceWidth → tableAt t∈tables) :
    ∃ indices : Nat → Nat → Nat,∀ t column,∀ hc : column<(tableAt t).sourceWidth,
      ∃ hi : indices t column<(tables.flatMap gkrMetadataLanes).length,
        (tables.flatMap gkrMetadataLanes)[indices t column]=metadataColumnLane (tableAt t) column ∧
        ∀ j,∀ hj : j<(tables.flatMap gkrMetadataLanes).length,
          (tables.flatMap gkrMetadataLanes)[j]=metadataColumnLane (tableAt t) column → j=indices t column := by
  classical
  have each : ∀ t column,∃ i,∀ hc : column<(tableAt t).sourceWidth,
      ∃ hi : i<(tables.flatMap gkrMetadataLanes).length,
        (tables.flatMap gkrMetadataLanes)[i]=metadataColumnLane (tableAt t) column ∧
        ∀ j,∀ hj : j<(tables.flatMap gkrMetadataLanes).length,
          (tables.flatMap gkrMetadataLanes)[j]=metadataColumnLane (tableAt t) column → j=i := by
    intro t column
    by_cases hc : column<(tableAt t).sourceWidth
    · obtain ⟨i,hi,same,unique⟩ := metadata_source_column_index tables disjoint (tableAt t)
        (member t (by omega)) column hc
      exact ⟨i,fun _=>⟨hi,same,unique⟩⟩
    · exact ⟨0,fun h=>False.elim (hc h)⟩
  exact ⟨fun t column=>Classical.choose (each t column),fun t column=>Classical.choose_spec (each t column)⟩

/-- Compose metadata index selection, decoded provenance and joint PCS
representatives into a single fixed base source trace. No externally chosen
index family or indexed provenance premise remains. -/
theorem metadata_joint_fixed_source_trace {A : Type}
    (layout : GKRJointLayout) (tables : List GKRTableMetadata)
    (disjoint : AllLaneSupportsDisjoint (tables.flatMap gkrMetadataLanes))
    (tableAt : Nat → GKRTableMetadata)
    (member : ∀ t,0<(tableAt t).sourceWidth → tableAt t∈tables)
    (valid : ∀ lane∈tables.flatMap gkrMetadataLanes,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout (tables.flatMap gkrMetadataLanes))
    (domain : List Fp8) (distinct : domain.Nodup) (basePoints : ∀ x∈domain,Fp8.IsBase x)
    (D T : Nat) (separation : 2*(domain.length-T)+D≤domain.length)
    (sourceOracles : Nat → Nat → Fp8 → Fp)
    (sources : A → List (Fp8 → Fp8)) (polys : A → List (Poly Fp8))
    (decoded : A → Trace Fp8) (eligible : A → Prop)
    (sourceShape : ∀ a,eligible a → (sources a).length=(tables.flatMap gkrMetadataLanes).length)
    (representative : ∀ a,eligible a →
      JointBetaRepresentative domain (fun _=>1) (heterogeneousJointDimension layout) D T
        ((tables.flatMap gkrMetadataLanes).map (heterogeneousJointBeta layout)) (sources a) (polys a))
    (fixedOracle : ∀ a,eligible a → ∀ t column,column<(tableAt t).sourceWidth →
      ∀ i,∀ hi : i<(tables.flatMap gkrMetadataLanes).length,
        (tables.flatMap gkrMetadataLanes)[i]=metadataColumnLane (tableAt t) column →
        (sources a).getD i (fun _=>0)=(fun x=>Fp8.ofBase (sourceOracles t column x)))
    (logs : ∀ a,eligible a → (decoded a).log=(fun t=>(tableAt t).rowLog))
    (provenance : ∀ a,eligible a → ∀ t column,column<(tableAt t).sourceWidth →
      ∃ polynomial : Poly Fp8,
        (metadataColumnLane (tableAt t) column,polynomial)∈(tables.flatMap gkrMetadataLanes).zip (polys a) ∧
        (fun row=>(decoded a).cell t row column)=
          recoveredColumnValues layout.commonLog (metadataColumnLane (tableAt t) column)
            (metadataColumnOffset (tableAt t) column) polynomial) :
    ∃ source : Trace Fp,source.log=(fun t=>(tableAt t).rowLog) ∧
      ∀ a,eligible a → (decoded a).log=source.log ∧
        ∀ t row column,column<(tableAt t).sourceWidth →
          (decoded a).cell t row column=Fp8.ofBase (source.cell t row column) := by
  obtain ⟨indices,indexSpec⟩ := metadata_source_index_family tables disjoint tableAt member
  have indexBound := fun t column hc=>(indexSpec t column hc).choose
  apply fixed_joint_representative_source_trace layout (tables.flatMap gkrMetadataLanes) valid geometry
    domain distinct basePoints D T separation (fun t=>(tableAt t).rowLog)
    (fun t=>(tableAt t).sourceWidth) indices (fun t column=>metadataColumnOffset (tableAt t) column)
    indexBound sourceOracles sources polys decoded eligible sourceShape representative
  · intro a ha t column hc
    exact fixedOracle a ha t column hc (indices t column) (indexBound t column hc)
      (indexSpec t column hc).choose_spec.1
  · exact logs
  · intro a ha t row column hc
    exact decoded_source_indexed_provenance layout.commonLog tables (polys a)
      ((representative a ha).1.trans (sourceShape a ha)) (tableAt t) column
      (fun column row=>(decoded a).cell t row column) (indices t column) (indexBound t column hc)
      (indexSpec t column hc).choose_spec.1 (indexSpec t column hc).choose_spec.2
      (provenance a ha t column hc) row

end NearCompression
