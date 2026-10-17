import NearCompression.CachedBlockSequence

/-! Cached payload witness generation with exact reference correspondence. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def cachedWriteBytesWitness (hash : Bytes → ByteArray) (s : St) (block count depth address : Nat)
    (data : ByteArray) : List PageBatchWitness :=
  cachedBlockSequence hash block depth
    (cachePageTree (blockTreeHash hash block) (buildSubpageTree s block count depth))
    (groupBlockRequests block (byteWriteRequests address data))

theorem in_bounds_block_plan_valid (s : St) (block count address : Nat) (positive : 0 < block)
    (layout : block * count = pageSize) (data : ByteArray)
    (inBounds : address + data.size ≤ s.pages.size * pageSize) :
    blockPlanValid block (s.pages.size * count) (groupBlockRequests block (byteWriteRequests address data)) := by
  apply grouped_block_requests_valid block _ positive
  intro r member
  obtain ⟨i, hi, equal⟩ := List.mem_map.mp member
  subst r
  have hib : i < data.size := by simpa [List.mem_range'] using hi
  apply global_block_allocated s.pages (address + i) block count layout
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < pageSize)).mpr
  omega

theorem cached_write_bytes_witness_exact (hash : Bytes → ByteArray) (s : St) (full : fullPages s.pages)
    (block count depth address : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (capacity : s.pages.size * count ≤ 2 ^ depth) (data : ByteArray)
    (inBounds : address + data.size ≤ s.pages.size * pageSize) :
    cachedWriteBytesWitness hash s block count depth address data =
      honestWriteBytesWitness hash s block count depth address data := by
  exact cached_block_sequence_exact hash block count depth positive layout s full capacity _
    (in_bounds_block_plan_valid s block count address positive layout data inBounds)

theorem cached_write_bytes_witness_accepted (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (s : St) (full : fullPages s.pages)
    (block count depth address : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (capacity : s.pages.size * count ≤ 2 ^ depth) (data : ByteArray)
    (inBounds : address + data.size ≤ s.pages.size * pageSize) :
    checkBlockBatchedWriteBytes hash (describeSubpageMemory hash s block count depth) address data
      (cachedWriteBytesWitness hash s block count depth address data) =
      some (describeSubpageMemory hash (writeBytes s address data) block count depth) := by
  rw [cached_write_bytes_witness_exact hash s full block count depth address positive layout capacity data inBounds]
  exact honest_write_bytes_witness_accepted hash digestBound s full block count depth address
    positive layout capacity data inBounds

end NearCompression
