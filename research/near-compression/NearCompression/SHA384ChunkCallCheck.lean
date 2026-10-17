import NearCompression.SHA384ChunkCallChain
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

/-- Full 512-bit state links; never truncate an intermediate state to384bits. -/
def checkChunkCallWiring (nodes : List Nat) (payload : Nat→Nat→Fp)
    (initial : List Nat) : List (Nat × List Nat)→List Nat→Bool
  | [],final => final==initial
  | item::rest,final =>
      (sharedFlatWords (chunkGlobalUseRow nodes payload item.1) 3 8==initial) &&
      checkChunkCallWiring nodes payload
        (sharedFlatWords (chunkGlobalUseRow nodes payload item.1) 99 8) rest final

theorem check_chunk_call_wiring_iff (nodes : List Nat) (payload : Nat→Nat→Fp)
    (items : List (Nat × List Nat)) (initial final : List Nat) :
    checkChunkCallWiring nodes payload initial items final=true ↔
      chunkCallWiring nodes payload initial items final := by
  induction items generalizing initial with
  | nil => simp [checkChunkCallWiring,chunkCallWiring]
  | cons item rest ih => simp [checkChunkCallWiring,chunkCallWiring,ih]

/-- Deterministic call checker. Compression validity and ordered-use commitment
binding are separate obligations. Message bytes must come from verifier operands. -/
def checkChunkCall (nodes : List Nat) (payload : Nat→Nat→Fp)
    (message : ArenaCore.Bytes) (items : List (Nat × List Nat)) (final : List Nat) : Bool :=
  items.all (fun item=>decide (item.1<nodes.length ∧ item.2.length=128) &&
    (sharedFlatWords (chunkGlobalUseRow nodes payload item.1) 35 16==words item.2)) &&
  ((items.map Prod.snd).flatten==pad (message.map UInt8.toNat)) &&
  checkChunkCallWiring nodes payload sha384ChainIV items final

theorem check_chunk_call_sound (nodes : List Nat) (payload : Nat→Nat→Fp)
    (message : ArenaCore.Bytes) (items : List (Nat × List Nat)) (final : List Nat)
    (checked : checkChunkCall nodes payload message items final=true) :
    (∀ item,item∈items → item.1<nodes.length) ∧
    (∀ item,item∈items → item.2.length=128) ∧
    (items.map Prod.snd).flatten=pad (message.map UInt8.toNat) ∧
    (∀ item,item∈items → sharedFlatWords (chunkGlobalUseRow nodes payload item.1) 35 16=words item.2) ∧
    chunkCallWiring nodes payload sha384ChainIV items final := by
  simp only [checkChunkCall,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,beq_iff_eq] at checked
  exact ⟨fun item hi=>(checked.1.1 item hi).1.1,
    fun item hi=>(checked.1.1 item hi).1.2,checked.1.2,
    fun item hi=>(checked.1.1 item hi).2,
    (check_chunk_call_wiring_iff nodes payload items sha384ChainIV final).mp checked.2⟩

/-- Chunk AIR soundness plus the executable call checker yields full SHA384.
Ordered-use root binding and operand provenance remain explicit. -/
theorem sha384_chunks_checked_call_sound (nodes : List Nat) (payload : Nat→Nat→Fp)
    (total capacity chunks : Nat) (fanoutBits : Nat→Nat) (traces : Nat→Trace Fp)
    (positive : 0<capacity) (capacitySmall : capacity<P) (totalSmall : total<P)
    (coverage : total≤chunks*capacity) (nodeBound : ∀ i,i<nodes.length → nodes.getD i 0<total)
    (useBound : nodes.length<P)
    (claims : ∀ c,c<chunks → 0<chunkNodeCount total capacity c →
      HoldsP (sha384NodeChunkAir (capacity*c) (chunkNodeCount total capacity c) (fanoutBits c)
        (chunkOrdinals nodes capacity c).length) [] (traces c))
    (binding : SHA384ChunkUseBinding nodes payload capacity chunks traces)
    (message : ArenaCore.Bytes) (items : List (Nat × List Nat)) (final : List Nat)
    (checked : checkChunkCall nodes payload message items final=true) :
    (digestBytes final).take 48=sha384ChainDigest message := by
  obtain ⟨declared,lengths,canonical,messageWords,wiring⟩ :=
    check_chunk_call_sound nodes payload message items final checked
  exact sha384_chunks_call_sound nodes payload total capacity chunks fanoutBits traces
    positive capacitySmall totalSmall coverage nodeBound useBound claims binding
    message items final declared lengths canonical messageWords wiring

end NearCompression
