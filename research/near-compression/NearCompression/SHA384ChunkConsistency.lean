import NearCompression.SHA384ChunkComposition
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

/-- Equal global tags in two declared rows force identical complete record
payloads, including all hidden output-state words. No payload equality premise. -/
theorem sha384_chunk_repeated_use (base count bits uses : Nat) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) [] tr)
    (positive : 0<count) (small : count<P) (useSmall : uses<P)
    (r s : Nat) (hr : r<uses) (hs : s<uses)
    (tags : tr.cell 3 r 2=tr.cell 3 s 2) :
    ∀ j,j<176 → tr.cell 3 r (3+j)=tr.cell 3 s (3+j) := by
  have pf := sha384_chunk_use_prefix base count bits uses [] tr h (by omega) useSmall
  have cap := shared_prefix_capacity pf
  obtain ⟨a,ha,ta,va⟩ := sha384_chunk_use_cells base count bits uses [] tr h positive small
    r (by omega) (shared_prefix_required pf r (by omega) hr)
  obtain ⟨b,hb,tb,vb⟩ := sha384_chunk_use_cells base count bits uses [] tr h positive small
    s (by omega) (shared_prefix_required pf s (by omega) hs)
  have cast : Fp.ofNat a=Fp.ofNat b := by
    have eq := ta.trans (tags.trans tb.symm)
    grind
  have natEq := congrArg Fp.toNat cast
  simp only [Fp.toNat_ofNat, Nat.mod_eq_of_lt (show a<P by omega),
    Nat.mod_eq_of_lt (show b<P by omega)] at natEq
  subst b
  intro j hj
  exact (va j hj).trans (vb j hj).symm

/-- Binding to deterministic ordered subsequences plus actual component AIR
forces all176 payload fields to agree whenever global node IDs repeat. -/
theorem sha384_chunks_repeated_node_payload (nodes : List Nat) (payload : Nat→Nat→Fp)
    (total capacity chunks : Nat) (fanoutBits : Nat→Nat) (traces : Nat→Trace Fp)
    (positive : 0<capacity) (capacitySmall : capacity<P)
    (coverage : total≤chunks*capacity) (nodeBound : ∀ i,i<nodes.length → nodes.getD i 0<total)
    (useBound : nodes.length<P)
    (claims : ∀ c,c<chunks → 0<chunkNodeCount total capacity c →
      HoldsP (sha384NodeChunkAir (capacity*c) (chunkNodeCount total capacity c) (fanoutBits c)
        (chunkOrdinals nodes capacity c).length) [] (traces c))
    (binding : SHA384ChunkUseBinding nodes payload capacity chunks traces)
    (i k : Nat) (hi : i<nodes.length) (hk : k<nodes.length)
    (same : nodes.getD i 0=nodes.getD k 0) :
    ∀ j,j<176 → payload i j=payload k j := by
  let owner := chunkOwner nodes capacity i
  have owners : chunkOwner nodes capacity k=owner := by
    simp only [owner,chunkOwner,same]
  have bound : owner<chunks := chunk_owner_bound nodes capacity chunks i positive
    (by intro a ha;have b:=nodeBound a ha;omega) hi
  have interval := chunk_owner_interval total capacity (nodes.getD i 0) positive (nodeBound i hi)
  have cp : 0<chunkNodeCount total capacity owner := interval.1
  have cs : chunkNodeCount total capacity owner<P :=
    Nat.lt_of_le_of_lt (chunk_node_count_le total capacity owner) capacitySmall
  have lengthBound : (chunkOrdinals nodes capacity owner).length≤nodes.length := by
    have filtered := List.length_filter_le (p:=fun a=>nodes.getD a 0/capacity==owner) (l:=List.range nodes.length)
    simpa only [chunkOrdinals,List.length_range] using filtered
  have li := (chunk_ordinal_location nodes capacity i hi).1
  have lk := (chunk_ordinal_location nodes capacity k hk).1
  rw [owners] at lk
  have fi := chunk_binding_at_ordinal nodes payload capacity chunks traces binding i hi bound
  have fk := chunk_binding_at_ordinal nodes payload capacity chunks traces binding k hk (by rw [owners];exact bound)
  rw [owners] at fk
  have tags : (traces owner).cell 3 (chunkLocalRow nodes capacity i) 2=
      (traces owner).cell 3 (chunkLocalRow nodes capacity k) 2 := by
    have a:=fi 0 (by omega)
    have b:=fk 0 (by omega)
    simp only [Nat.add_zero,chunkGlobalUseRow,ite_true] at a b
    exact a.trans ((congrArg Fp.ofNat same).trans b.symm)
  have values := sha384_chunk_repeated_use (capacity*owner) (chunkNodeCount total capacity owner)
    (fanoutBits owner) (chunkOrdinals nodes capacity owner).length (traces owner)
    (claims owner bound cp) cp cs (by omega) _ _ li lk tags
  intro j hj
  have a:=fi (1+j) (by omega)
  have b:=fk (1+j) (by omega)
  have neq : 3+j≠2 := by omega
  have range : 3≤3+j ∧ 3+j<179 := by omega
  simp only [←Nat.add_assoc,chunkGlobalUseRow,ite_eq_right neq,ite_eq_left range,
    Nat.add_sub_cancel_left] at a b
  exact a.symm.trans ((values j hj).trans b)
end NearCompression
