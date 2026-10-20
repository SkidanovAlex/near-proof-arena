import NearCompression.HeterogeneousGKRWeights

/-! Executable shape certificates for compiler-exported table metadata.
The checker discharges lane WellFormed bounds. Equality to the configured
compiler's table placement is a separate canonical-export check. -/
namespace NearCompression

structure GKRTableMetadata where
  rowLog : Nat
  rowOffset : Nat
  blockOffset : Nat
  columnCapacity : Nat
  sourceWidth : Nat
  auxiliaryWidth : Nat
  sourcePackingLog : Nat
  auxiliaryPackingLog : Nat

def gkrTableMetadataCheck (layout : GKRJointLayout) (table : GKRTableMetadata) : Bool :=
  decide (table.rowOffset+table.rowLog≤layout.rowCoordinates) &&
  decide (table.rowLog+table.sourcePackingLog≤layout.commonLog) &&
  decide (table.auxiliaryWidth=0 ∨ table.rowLog+table.auxiliaryPackingLog≤layout.commonLog) &&
  decide (table.sourceWidth+table.auxiliaryWidth≤table.columnCapacity) &&
  decide (table.blockOffset+2*table.columnCapacity≤layout.privateCapacity) &&
  decide (layout.privateCapacity≤2^layout.inputLog)

def gkrMetadataLane (table : GKRTableMetadata) (auxiliary : Bool) (group : Nat) : GKRSourceLane where
  rowLog := table.rowLog
  packingLog := if auxiliary then table.auxiliaryPackingLog else table.sourcePackingLog
  rowOffset := table.rowOffset
  inputStart := table.blockOffset+(if auxiliary then table.sourceWidth else 0)
  nextOffset := table.columnCapacity
  width := if auxiliary then table.auxiliaryWidth else table.sourceWidth
  group := group

/-- Accepted numerical metadata generates valid source and nonempty auxiliary
lane descriptors. No lane-validity proposition is supplied by the caller. -/
theorem checked_table_metadata_lane (layout : GKRJointLayout) (table : GKRTableMetadata)
    (checked : gkrTableMetadataCheck layout table=true) (auxiliary : Bool) (group : Nat)
    (nonemptyAuxiliary : auxiliary=true → 0<table.auxiliaryWidth) :
    (gkrMetadataLane table auxiliary group).WellFormed layout := by
  simp only [gkrTableMetadataCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨⟨rows,source⟩,aux⟩,width⟩,capacity⟩,envelope⟩ := checked
  cases auxiliary with
  | false =>
    simp only [GKRSourceLane.WellFormed,gkrMetadataLane,Bool.false_eq_true,ite_false,Nat.add_zero]
    exact ⟨rows,source,by omega,by omega,envelope⟩
  | true =>
    have positive := nonemptyAuxiliary rfl
    simp only [GKRSourceLane.WellFormed,gkrMetadataLane,ite_true]
    exact ⟨rows,by omega,by omega,by omega,envelope⟩

def gkrMetadataLanes (table : GKRTableMetadata) : List GKRSourceLane :=
  ((List.range ((table.sourceWidth+2^table.sourcePackingLog-1)/2^table.sourcePackingLog)).map
    (gkrMetadataLane table false)) ++
  ((List.range ((table.auxiliaryWidth+2^table.auxiliaryPackingLog-1)/2^table.auxiliaryPackingLog)).map
    (gkrMetadataLane table true))

/-- The exact ceil(width/packing) source-then-auxiliary lane enumeration
satisfies the fixed-envelope heterogeneous proof's public shape contract. -/
theorem checked_table_metadata_lanes (layout : GKRJointLayout) (table : GKRTableMetadata)
    (checked : gkrTableMetadataCheck layout table=true) :
    ∀ lane∈gkrMetadataLanes table,lane.WellFormed layout := by
  intro lane member
  simp only [gkrMetadataLanes,List.mem_append,List.mem_map] at member
  rcases member with ⟨group,hg,rfl⟩ | ⟨group,hg,rfl⟩
  · exact checked_table_metadata_lane layout table checked false group (by simp)
  · apply checked_table_metadata_lane layout table checked true group
    intro yes
    have bound := List.mem_range.mp hg
    by_cases positive : 0<table.auxiliaryWidth
    · exact positive
    · have width : table.auxiliaryWidth=0 := by omega
      have small : (2^table.auxiliaryPackingLog-1)/2^table.auxiliaryPackingLog=0 :=
        Nat.div_eq_of_lt (by have pos := Nat.two_pow_pos table.auxiliaryPackingLog; omega)
      simp only [width,Nat.zero_add,small] at bound
      omega

/-- A list of accepted exported table certificates discharges every lane
bound required by heterogeneous_betas_affine and its tensor/counting theorems. -/
theorem checked_metadata_all_lanes (layout : GKRJointLayout) (tables : List GKRTableMetadata)
    (checked : tables.all (gkrTableMetadataCheck layout)=true) :
    ∀ lane∈tables.flatMap gkrMetadataLanes,lane.WellFormed layout := by
  intro lane member
  obtain ⟨table,ht,hl⟩ := List.mem_flatMap.mp member
  exact checked_table_metadata_lanes layout table (List.all_eq_true.mp checked table ht) lane hl

end NearCompression
