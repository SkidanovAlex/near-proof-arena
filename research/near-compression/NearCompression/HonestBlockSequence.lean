import NearCompression.HonestBlockBatch

/-! Reference generation of state-dependent openings for an ordered batch plan. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

structure BlockBatchPlan where
  index : Nat
  writes : List (Nat × UInt8)

def blockPlanRequests (block : Nat) : List BlockBatchPlan → List (Nat × UInt8)
  | [] => []
  | p :: ps => blockBatchRequests block p.index p.writes ++ blockPlanRequests block ps

def honestBlockSequence (hash : Bytes → ByteArray) (block count depth : Nat) :
    St → List BlockBatchPlan → List PageBatchWitness
  | _, [] => []
  | s, p :: ps => honestBlockBatch hash s block count depth p.index p.writes ::
      honestBlockSequence hash block count depth
        (executeByteRequests s (blockBatchRequests block p.index p.writes)) ps

theorem honest_block_sequence_requests (hash : Bytes → ByteArray) (block count depth : Nat)
    (s : St) (plan : List BlockBatchPlan) :
    blockBatchSequenceRequests block (honestBlockSequence hash block count depth s plan) =
      blockPlanRequests block plan := by
  induction plan generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [honestBlockSequence, blockBatchSequenceRequests, honestBlockBatch, blockPlanRequests, ih]

theorem honest_block_sequence_accepted (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (block count depth : Nat)
    (positive : 0 < block) (layout : block * count = pageSize)
    (s : St) (full : fullPages s.pages) (capacity : s.pages.size * count ≤ 2 ^ depth)
    (plan : List BlockBatchPlan)
    (valid : ∀ p ∈ plan, p.index < s.pages.size * count ∧ ∀ w ∈ p.writes, w.1 < block) :
    checkBlockBatches hash (describeSubpageMemory hash s block count depth)
      (honestBlockSequence hash block count depth s plan) =
      some (describeSubpageMemory hash (executeByteRequests s (blockPlanRequests block plan)) block count depth) := by
  induction plan generalizing s with
  | nil => rfl
  | cons p ps ih =>
    have hp := valid p (by simp)
    have first := honest_block_batch_accepted hash digestBound s full block count depth p.index
      positive layout capacity hp.1 p.writes hp.2
    simp only [honestBlockSequence, checkBlockBatches, first, Option.bind_some]
    have tailValid : ∀ q ∈ ps,
        q.index < (executeByteRequests s (blockBatchRequests block p.index p.writes)).pages.size * count ∧
        ∀ w ∈ q.writes, w.1 < block := by
      intro q hq
      rw [execute_byte_requests_page_count]
      exact valid q (by simp [hq])
    have tail := ih (executeByteRequests s (blockBatchRequests block p.index p.writes))
      (execute_requests_full_pages s full _) (by simpa only [execute_byte_requests_page_count] using capacity)
      tailValid
    simpa only [blockPlanRequests, executeByteRequests, List.foldl_append] using tail

theorem honest_block_batched_bytes_accepted (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (block count depth : Nat)
    (positive : 0 < block) (layout : block * count = pageSize)
    (s : St) (full : fullPages s.pages) (capacity : s.pages.size * count ≤ 2 ^ depth)
    (address : Nat) (data : ByteArray) (plan : List BlockBatchPlan)
    (valid : ∀ p ∈ plan, p.index < s.pages.size * count ∧ ∀ w ∈ p.writes, w.1 < block)
    (requests : blockPlanRequests block plan = byteWriteRequests address data) :
    checkBlockBatchedWriteBytes hash (describeSubpageMemory hash s block count depth) address data
      (honestBlockSequence hash block count depth s plan) =
      some (describeSubpageMemory hash (writeBytes s address data) block count depth) := by
  unfold checkBlockBatchedWriteBytes
  change (if blockBatchSequenceRequests block (honestBlockSequence hash block count depth s plan) =
      byteWriteRequests address data then _ else _) = _
  rw [honest_block_sequence_requests, requests, if_pos rfl]
  rw [honest_block_sequence_accepted hash digestBound block count depth positive layout s full capacity plan valid,
    requests, ← write_bytes_requests_exact]

end NearCompression
