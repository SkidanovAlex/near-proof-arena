import NearCompression.SHA384NodeChunkUse

namespace NearCompression

/-- Ordered global use ordinals assigned to a fixed-width global node interval.
Identical records retain distinct ordinals and are never deduplicated here. -/
def chunkOrdinals (nodes : List Nat) (capacity chunk : Nat) : List Nat :=
  (List.range nodes.length).filter (fun i=>nodes.getD i 0/capacity==chunk)

def chunkOwner (nodes : List Nat) (capacity ordinal : Nat) : Nat := nodes.getD ordinal 0/capacity

def chunkLocalRow (nodes : List Nat) (capacity ordinal : Nat) : Nat :=
  (chunkOrdinals nodes capacity (chunkOwner nodes capacity ordinal)).idxOf ordinal

theorem chunk_ordinal_membership (nodes : List Nat) (capacity chunk ordinal : Nat) :
    ordinal∈chunkOrdinals nodes capacity chunk ↔ ordinal<nodes.length ∧ chunkOwner nodes capacity ordinal=chunk := by
  simp [chunkOrdinals,chunkOwner,List.mem_filter]

theorem chunk_ordinals_nodup (nodes : List Nat) (capacity chunk : Nat) :
    (chunkOrdinals nodes capacity chunk).Nodup :=
  List.Nodup.sublist List.filter_sublist List.nodup_range

/-- Within each chunk, the actual original use order is preserved. -/
theorem chunk_ordinals_ordered (nodes : List Nat) (capacity chunk : Nat) :
    (chunkOrdinals nodes capacity chunk).Pairwise (fun a b=>a<b) :=
  List.Pairwise.filter _ List.pairwise_lt_range

theorem chunk_owner_bound (nodes : List Nat) (capacity chunks ordinal : Nat)
    (positive : 0<capacity) (bounded : ∀ i,i<nodes.length → nodes.getD i 0<chunks*capacity)
    (hi : ordinal<nodes.length) : chunkOwner nodes capacity ordinal<chunks := by
  exact (Nat.div_lt_iff_lt_mul positive).mpr (bounded ordinal hi)

/-- Every original ordinal has a concrete in-range local position. -/
theorem chunk_ordinal_location (nodes : List Nat) (capacity ordinal : Nat) (hi : ordinal<nodes.length) :
    chunkLocalRow nodes capacity ordinal < (chunkOrdinals nodes capacity (chunkOwner nodes capacity ordinal)).length ∧
      (chunkOrdinals nodes capacity (chunkOwner nodes capacity ordinal)).getD (chunkLocalRow nodes capacity ordinal) 0=ordinal := by
  have member := (chunk_ordinal_membership nodes capacity (chunkOwner nodes capacity ordinal) ordinal).mpr ⟨hi,rfl⟩
  have bound := List.idxOf_lt_length_iff.mpr member
  refine ⟨bound,?_⟩
  simp [List.getD,bound,chunkLocalRow]

/-- No ordinal can appear twice, either within a chunk or across chunks. -/
theorem chunk_ordinal_unique (nodes : List Nat) (capacity ordinal chunk row : Nat)
    (hi : ordinal<nodes.length) (hr : row<(chunkOrdinals nodes capacity chunk).length)
    (eq : (chunkOrdinals nodes capacity chunk).getD row 0=ordinal) :
    chunk=chunkOwner nodes capacity ordinal ∧ row=chunkLocalRow nodes capacity ordinal := by
  have elem : (chunkOrdinals nodes capacity chunk)[row]=ordinal := by simpa [List.getD,hr] using eq
  have member : ordinal∈chunkOrdinals nodes capacity chunk := elem ▸ List.getElem_mem hr
  have owner := ((chunk_ordinal_membership nodes capacity chunk ordinal).mp member).2
  subst chunk
  have location := chunk_ordinal_location nodes capacity ordinal hi
  refine ⟨rfl,?_⟩
  have found : (chunkOrdinals nodes capacity (chunkOwner nodes capacity ordinal))[chunkLocalRow nodes capacity ordinal]=ordinal := by
    simpa [List.getD,location.1] using location.2
  exact (chunk_ordinals_nodup nodes capacity (chunkOwner nodes capacity ordinal)).getElem_inj.mp (elem.trans found.symm)

/-- Finite exact coverage, with an explicit unique chunk/local-row coordinate. -/
theorem chunk_ordinal_coverage (nodes : List Nat) (capacity chunks ordinal : Nat)
    (positive : 0<capacity) (bounded : ∀ i,i<nodes.length → nodes.getD i 0<chunks*capacity)
    (hi : ordinal<nodes.length) :
    ∃ chunk,chunk<chunks ∧ ∃ row,row<(chunkOrdinals nodes capacity chunk).length ∧
      (chunkOrdinals nodes capacity chunk).getD row 0=ordinal ∧
      ∀ c r,c<chunks → r<(chunkOrdinals nodes capacity c).length →
        (chunkOrdinals nodes capacity c).getD r 0=ordinal → c=chunk ∧ r=row := by
  have loc := chunk_ordinal_location nodes capacity ordinal hi
  exact ⟨chunkOwner nodes capacity ordinal,chunk_owner_bound nodes capacity chunks ordinal positive bounded hi,
    chunkLocalRow nodes capacity ordinal,loc.1,loc.2,fun c r _ hr eq=>chunk_ordinal_unique nodes capacity ordinal c r hi hr eq⟩

/-- Reading chunk coordinates in original ordinal order exactly reconstructs
all original values, including duplicate values and their multiplicities. -/
theorem chunk_reconstruct_values {α : Type} (nodes : List Nat) (capacity : Nat) (value : Nat→α) :
    (List.range nodes.length).map (fun i=>value ((chunkOrdinals nodes capacity (chunkOwner nodes capacity i)).getD
      (chunkLocalRow nodes capacity i) 0))=(List.range nodes.length).map value := by
  apply List.map_congr_left
  intro i hi
  rw [(chunk_ordinal_location nodes capacity i (List.mem_range.mp hi)).2]

end NearCompression
