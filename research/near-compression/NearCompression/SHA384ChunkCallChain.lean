import NearCompression.SHA384ChunkComposition
import NearCompression.SHA384Chain
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

/-- Compression observes the sixteen block words, so word equality is enough;
no injectivity assumption about arbitrary byte lists is required. -/
theorem sha384_compress_words_congr (state left right : List Nat)
    (h : words left=words right) : compress state left=compress state right := by
  simp only [compress,h]

/-- Exact consumption helper for a list of complete blocks. -/
theorem sha384_exact_block_fold (parts : List (List Nat)) (initial : List Nat)
    (lengths : ∀ b,b∈parts → b.length=128) :
    parts.foldl compress initial=blocks parts.length initial parts.flatten := by
  induction parts generalizing initial with
  | nil => rfl
  | cons b rest ih =>
    change rest.foldl compress (compress initial b)=
      blocks (rest.length+1) initial (b++rest.flatten)
    rw [sha512_blocks_cons_exact _ _ _ _ (lengths b (by simp))]
    exact ih _ (by intro x hx;exact lengths x (by simp [hx]))

/-- Each declared canonical block obtains its compression fact from the actual
chunk AIR. Framing/operand equality and commitment binding remain explicit. -/
theorem sha384_chunks_canonical_compression (nodes : List Nat) (payload : Nat→Nat→Fp)
    (total capacity chunks : Nat) (fanoutBits : Nat→Nat) (traces : Nat→Trace Fp)
    (positive : 0<capacity) (capacitySmall : capacity<P) (totalSmall : total<P)
    (coverage : total≤chunks*capacity) (nodeBound : ∀ i,i<nodes.length → nodes.getD i 0<total)
    (useBound : nodes.length<P)
    (claims : ∀ c,c<chunks → 0<chunkNodeCount total capacity c →
      HoldsP (sha384NodeChunkAir (capacity*c) (chunkNodeCount total capacity c) (fanoutBits c)
        (chunkOrdinals nodes capacity c).length) [] (traces c))
    (binding : SHA384ChunkUseBinding nodes payload capacity chunks traces)
    (ordinal : Nat) (hi : ordinal<nodes.length) (canonical : List Nat)
    (messageWords : sharedFlatWords (chunkGlobalUseRow nodes payload ordinal) 35 16=words canonical) :
    sharedFlatWords (chunkGlobalUseRow nodes payload ordinal) 99 8=
      compress (sharedFlatWords (chunkGlobalUseRow nodes payload ordinal) 3 8) canonical := by
  obtain ⟨block,_,_,m,c,_⟩ := sha384_chunks_global_use_sound nodes payload total capacity chunks
    fanoutBits traces positive capacitySmall totalSmall coverage nodeBound useBound claims binding ordinal hi
  exact c.trans (sha384_compress_words_congr _ _ _ (m.symm.trans messageWords))

def chunkCallWiring (nodes : List Nat) (payload : Nat→Nat→Fp)
    (initial : List Nat) : List (Nat × List Nat) → List Nat → Prop
  | [],final => final=initial
  | item::rest,final =>
      sharedFlatWords (chunkGlobalUseRow nodes payload item.1) 3 8=initial ∧
      chunkCallWiring nodes payload
        (sharedFlatWords (chunkGlobalUseRow nodes payload item.1) 99 8) rest final

private theorem chunk_call_fold (nodes : List Nat) (payload : Nat→Nat→Fp)
    (items : List (Nat × List Nat)) (initial final : List Nat)
    (wiring : chunkCallWiring nodes payload initial items final)
    (facts : ∀ item,item∈items →
      sharedFlatWords (chunkGlobalUseRow nodes payload item.1) 99 8=
        compress (sharedFlatWords (chunkGlobalUseRow nodes payload item.1) 3 8) item.2) :
    final=(items.map Prod.snd).foldl compress initial := by
  induction items generalizing initial with
  | nil => exact wiring
  | cons item rest ih =>
    have head := facts item (by simp)
    rw [wiring.1] at head
    have tail := ih _ wiring.2 (by intro x hx;exact facts x (by simp [hx]))
    simpa only [List.map_cons,List.foldl_cons,head] using tail

/-- Full SHA384 semantic composition for one ordered call. Every compression
fact is discharged by actual chunk HoldsP. The block list/operand framing,
full-state wiring and ordered-use binding are explicit interfaces, not claimed
as consequences of a commitment or of a Python replay certificate. -/
theorem sha384_chunks_call_sound (nodes : List Nat) (payload : Nat→Nat→Fp)
    (total capacity chunks : Nat) (fanoutBits : Nat→Nat) (traces : Nat→Trace Fp)
    (positive : 0<capacity) (capacitySmall : capacity<P) (totalSmall : total<P)
    (coverage : total≤chunks*capacity) (nodeBound : ∀ i,i<nodes.length → nodes.getD i 0<total)
    (useBound : nodes.length<P)
    (claims : ∀ c,c<chunks → 0<chunkNodeCount total capacity c →
      HoldsP (sha384NodeChunkAir (capacity*c) (chunkNodeCount total capacity c) (fanoutBits c)
        (chunkOrdinals nodes capacity c).length) [] (traces c))
    (binding : SHA384ChunkUseBinding nodes payload capacity chunks traces)
    (message : ArenaCore.Bytes) (items : List (Nat × List Nat)) (final : List Nat)
    (declared : ∀ item,item∈items → item.1<nodes.length)
    (lengths : ∀ item,item∈items → item.2.length=128)
    (canonical : (items.map Prod.snd).flatten=pad (message.map UInt8.toNat))
    (messageWords : ∀ item,item∈items →
      sharedFlatWords (chunkGlobalUseRow nodes payload item.1) 35 16=words item.2)
    (wiring : chunkCallWiring nodes payload sha384ChainIV items final) :
    (digestBytes final).take 48=sha384ChainDigest message := by
  have facts := fun (item : Nat × List Nat) (hm : item∈items) => sha384_chunks_canonical_compression nodes payload total capacity chunks
    fanoutBits traces positive capacitySmall totalSmall coverage nodeBound useBound claims binding
    item.1 (declared item hm) item.2 (messageWords item hm)
  have folded := chunk_call_fold nodes payload items sha384ChainIV final wiring facts
  have lens : ∀ b,b∈items.map Prod.snd → b.length=128 := by
    intro b hb
    obtain ⟨item,hi,rfl⟩ := List.mem_map.mp hb
    exact lengths item hi
  rw [sha384_exact_block_fold _ _ lens,canonical,List.length_map] at folded
  have count : (pad (message.map UInt8.toNat)).length=128*items.length := by
    rw [←canonical]
    clear facts folded wiring canonical messageWords declared lens
    induction items with
    | nil => simp
    | cons item rest ih =>
      have head := lengths item (by simp)
      have tail := ih (by intro x hx;exact lengths x (by simp [hx]))
      simp only [List.map_cons,List.flatten_cons,List.length_append,List.length_cons,head,tail]
      omega
  dsimp only [sha384ChainDigest]
  rw [folded,count]
  congr 3
  omega

end NearCompression
