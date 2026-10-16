import NearCompression.GKRBooleanLaneSeparator
namespace NearCompression

/-- Actual ceil packing covers every original column, including the final
partial group. The returned lane/column are determined by div/mod. -/
theorem metadata_column_coverage (table : GKRTableMetadata) (auxiliary next : Bool)
    (column : Nat) (bound : column<(if auxiliary then table.auxiliaryWidth else table.sourceWidth)) :
    let packing := 2^(if auxiliary then table.auxiliaryPackingLog else table.sourcePackingLog)
    let lane := gkrMetadataLane table auxiliary (column/packing)
    lane∈gkrMetadataLanes table ∧ column%packing<packing ∧
      lane.group*packing+column%packing=column ∧
      lane.LiveSlot next (table.blockOffset+(if auxiliary then table.sourceWidth else 0)+
        (if next then table.columnCapacity else 0)+column) := by
  dsimp only
  let width := if auxiliary then table.auxiliaryWidth else table.sourceWidth
  let p := 2^(if auxiliary then table.auxiliaryPackingLog else table.sourcePackingLog)
  have positive : 0<p := Nat.two_pow_pos _
  have cp : column/p*p≤column := Nat.div_mul_le_self _ _
  have group : column/p<(width+p-1)/p := by
    apply (Nat.lt_div_iff_mul_lt positive).mpr
    change column/p*p < width+p-1-(p-1)
    change column<width at bound
    omega
  have member : gkrMetadataLane table auxiliary (column/p)∈gkrMetadataLanes table := by
    unfold gkrMetadataLanes
    cases auxiliary with
    | false => apply List.mem_append_left; apply List.mem_map.mpr; exact ⟨column/p,List.mem_range.mpr group,rfl⟩
    | true => apply List.mem_append_right; apply List.mem_map.mpr; exact ⟨column/p,List.mem_range.mpr group,rfl⟩
  refine ⟨member,Nat.mod_lt column positive,?_,?_⟩
  · change column/p*p+column%p=column
    rw [Nat.mul_comm]
    exact Nat.div_add_mod column p
  · refine ⟨column%p,Nat.mod_lt column positive,?_,?_⟩
    · change (column/p)*p+column%p<width
      rw [Nat.mul_comm,Nat.div_add_mod]
      exact bound
    · change table.blockOffset+(if auxiliary then table.sourceWidth else 0)+
        (if next then table.columnCapacity else 0)+(column/p)*p+column%p=_
      have div : column/p*p+column%p=column := by rw [Nat.mul_comm]; exact Nat.div_add_mod column p
      omega

/-- Div/mod identifies the unique packed group and offset coordinate for an
original column. This rules out duplicate ownership within one branch. -/
theorem packed_column_owner_unique (packing group offset column : Nat)
    (positive : 0<packing) (bound : offset<packing) (same : group*packing+offset=column) :
    group=column/packing ∧ offset=column%packing := by
  subst column
  constructor
  · rw [Nat.mul_comm group packing,Nat.mul_add_div positive,Nat.div_eq_of_lt bound,Nat.add_zero]
  · simp [Nat.add_mod,Nat.mod_eq_of_lt bound]
end NearCompression
