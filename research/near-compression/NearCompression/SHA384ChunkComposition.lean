import NearCompression.ChunkIntervalBounds
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

/-- A verifier-declared global use record: globalID plus full A32/M64/C32/D48.
The ordinal labels uses, including repeated equal payloads. Metadata columns are
not part of this record; each component AIR separately fixes its local prefix. -/
def chunkGlobalUseRow (nodes : List Nat) (payload : Nat→Nat→Fp) (ordinal col : Nat) : Fp :=
  if col=2 then Fp.ofNat (nodes.getD ordinal 0)
  else if 3≤col ∧ col<179 then payload ordinal (col-3) else 0

/-- Explicit unresolved commitment-binding interface. A caller-fixed root of
the deterministic ordered subsequence must imply this field equality for the
actual trace. This definition is NOT a cryptographic theorem or a presumed
routing/compression/call-chain correctness condition. -/
def SHA384ChunkUseBinding (nodes : List Nat) (payload : Nat→Nat→Fp) (capacity chunks : Nat)
    (traces : Nat→Trace Fp) : Prop :=
  ∀ chunk,chunk<chunks → ∀ row,row<(chunkOrdinals nodes capacity chunk).length →
    ∀ j,j<177 → (traces chunk).cell 3 row (2+j)=
      chunkGlobalUseRow nodes payload ((chunkOrdinals nodes capacity chunk).getD row 0) (2+j)

theorem chunk_binding_at_ordinal (nodes : List Nat) (payload : Nat→Nat→Fp) (capacity chunks : Nat)
    (traces : Nat→Trace Fp) (binding : SHA384ChunkUseBinding nodes payload capacity chunks traces)
    (ordinal : Nat) (hi : ordinal<nodes.length) (hc : chunkOwner nodes capacity ordinal<chunks) :
    ∀ j,j<177 → (traces (chunkOwner nodes capacity ordinal)).cell 3 (chunkLocalRow nodes capacity ordinal) (2+j)=
      chunkGlobalUseRow nodes payload ordinal (2+j) := by
  have loc := chunk_ordinal_location nodes capacity ordinal hi
  intro j hj
  have eq := binding _ hc _ loc.1 j hj
  rwa [loc.2] at eq

/-- Coordinate transport covers every complete state/block word and digest byte. -/
theorem chunk_use_field_transport (row expected : Nat→Fp)
    (fields : ∀ j,j<177 → row (2+j)=expected (2+j)) :
    sharedFlatWords row 3 8=sharedFlatWords expected 3 8 ∧
      sharedFlatWords row 35 16=sharedFlatWords expected 35 16 ∧
      sharedFlatWords row 99 8=sharedFlatWords expected 99 8 ∧
      (List.range 48).map (fun j=>(row (131+j)).toNat)=
        (List.range 48).map (fun j=>(expected (131+j)).toNat) := by
  refine ⟨?_,?_,?_,?_⟩
  · apply shared_flat_words_transfer
    intro j hj
    simpa only [←Nat.add_assoc] using fields (1+j) (by omega)
  · apply shared_flat_words_transfer
    intro j hj
    simpa only [←Nat.add_assoc] using fields (33+j) (by omega)
  · apply shared_flat_words_transfer
    intro j hj
    simpa only [←Nat.add_assoc] using fields (97+j) (by omega)
  · apply List.map_congr_left
    intro j hj
    have eq := fields (129+j) (by have bound:=List.mem_range.mp hj;omega)
    simpa only [←Nat.add_assoc] using congrArg Fp.toNat eq

/-- Conditional global compression certificate. All ordinal assignment and
coverage are deterministic, and every local compression fact comes from actual
HoldsP. Only the explicitly named root-to-ordered-trace binding remains open.
This does not establish call chaining, padding provenance, or recursive security. -/
theorem sha384_chunks_global_use_sound (nodes : List Nat) (payload : Nat→Nat→Fp)
    (total capacity chunks : Nat) (fanoutBits : Nat→Nat) (traces : Nat→Trace Fp)
    (positive : 0<capacity) (capacitySmall : capacity<P) (totalSmall : total<P)
    (coverage : total≤chunks*capacity) (nodeBound : ∀ i,i<nodes.length → nodes.getD i 0<total)
    (useBound : nodes.length<P)
    (claims : ∀ c,c<chunks → 0<chunkNodeCount total capacity c →
      HoldsP (sha384NodeChunkAir (capacity*c) (chunkNodeCount total capacity c) (fanoutBits c)
        (chunkOrdinals nodes capacity c).length) [] (traces c))
    (binding : SHA384ChunkUseBinding nodes payload capacity chunks traces)
    (ordinal : Nat) (hi : ordinal<nodes.length) :
    ∃ block : List Nat,block.length=128 ∧ (∀ byte,byte∈block → byte<256) ∧
      sharedFlatWords (chunkGlobalUseRow nodes payload ordinal) 35 16=words block ∧
      sharedFlatWords (chunkGlobalUseRow nodes payload ordinal) 99 8=
        compress (sharedFlatWords (chunkGlobalUseRow nodes payload ordinal) 3 8) block ∧
      ((digestBytes (sharedFlatWords (chunkGlobalUseRow nodes payload ordinal) 99 8)).take 48).map UInt8.toNat=
        (List.range 48).map (fun j=>(chunkGlobalUseRow nodes payload ordinal (131+j)).toNat) := by
  let owner := chunkOwner nodes capacity ordinal
  have ownerBound : owner<chunks := chunk_owner_bound nodes capacity chunks ordinal positive
    (by intro i h;have b:=nodeBound i h;omega) hi
  have interval := chunk_owner_interval total capacity (nodes.getD ordinal 0) positive (nodeBound ordinal hi)
  have countPositive : 0<chunkNodeCount total capacity owner := interval.1
  have countSmall : chunkNodeCount total capacity owner<P :=
    Nat.lt_of_le_of_lt (chunk_node_count_le total capacity owner) capacitySmall
  have nowrap : capacity*owner+chunkNodeCount total capacity owner≤P := by
    have bound := interval.2.1
    change capacity*owner+chunkNodeCount total capacity owner≤total at bound
    omega
  have lengthBound : (chunkOrdinals nodes capacity owner).length≤nodes.length := by
    have filtered := List.length_filter_le (p:=fun i=>nodes.getD i 0/capacity==owner) (l:=List.range nodes.length)
    simpa only [chunkOrdinals,List.length_range] using filtered
  have h := claims owner ownerBound countPositive
  have loc := chunk_ordinal_location nodes capacity ordinal hi
  obtain ⟨node,hn,tag,block,len,bytes,a,m,c,d⟩ := sha384_chunk_declared_use_sound
    (capacity*owner) (chunkNodeCount total capacity owner) (fanoutBits owner) (chunkOrdinals nodes capacity owner).length
    [] (traces owner) h countPositive countSmall nowrap (by omega) (chunkLocalRow nodes capacity ordinal) loc.1
  have fields := chunk_binding_at_ordinal nodes payload capacity chunks traces binding ordinal hi ownerBound
  have moved := chunk_use_field_transport _ _ fields
  refine ⟨block,len,bytes,?_,?_,?_⟩
  · rw [←moved.2.1]
    exact m
  · rw [←moved.2.2.1,←moved.1]
    exact c
  · rw [←moved.2.2.1,d,moved.2.2.2]

end NearCompression
