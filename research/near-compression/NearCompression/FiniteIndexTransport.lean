import NearCompression.WeightedConsistencyTransfer
namespace NearCompression

noncomputable def finitePointIndex {K : Type} (N : Nat) (point : Nat → K) (x : K) : Nat := by
  classical
  exact if h : ∃ i,i<N ∧ point i=x then Classical.choose h else 0

theorem finite_point_index_inverse {K : Type} (N : Nat) (point : Nat → K)
    (injective : ∀ i<N,∀ j<N,point i=point j → i=j) (i : Nat) (hi : i<N) :
    finitePointIndex N point (point i)=i := by
  classical
  have existsIndex : ∃ j,j<N ∧ point j=point i := ⟨i,hi,rfl⟩
  have chosen := Classical.choose_spec existsIndex
  simp only [finitePointIndex,dite_eq_left existsIndex]
  exact injective _ chosen.1 i hi chosen.2

theorem finite_point_domain_nodup {K : Type} (N : Nat) (point : Nat → K)
    (injective : ∀ i<N,∀ j<N,point i=point j → i=j) :
    ((List.range N).map point).Nodup := by
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp_of_mem (fun hi hj different equal =>
    different (injective _ (List.mem_range.mp hi) _ (List.mem_range.mp hj) equal)) List.nodup_range

/-- Exact transport of any weighted event, including expressions containing
both the original index and its field point. -/
theorem finite_index_mass_transport {K : Type} (N : Nat) (point : Nat → K)
    (injective : ∀ i<N,∀ j<N,point i=point j → i=j)
    (weight : Nat → Nat) (event : Nat → K → Prop) :
    consistencyMass ((List.range N).map point) (fun x => weight (finitePointIndex N point x))
      (fun x => event (finitePointIndex N point x) x)=
    consistencyMass (List.range N) weight (fun i => event i (point i)) := by
  classical
  unfold consistencyMass
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_def,finite_point_index_inverse N point injective i (List.mem_range.mp hi)]

theorem finite_index_weight_sum {K : Type} (N : Nat) (point : Nat → K)
    (injective : ∀ i<N,∀ j<N,point i=point j → i=j) (weight : Nat → Nat) :
    (((List.range N).map point).map (fun x => weight (finitePointIndex N point x))).sum=
      ((List.range N).map weight).sum := by
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_def,finite_point_index_inverse N point injective i (List.mem_range.mp hi)]

end NearCompression
