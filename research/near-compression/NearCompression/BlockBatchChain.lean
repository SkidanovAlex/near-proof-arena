import NearCompression.CheckedBlockBatch

/-! Ordered block batches with exact binding to actual writeBytes requests.
The witness producer chooses grouping; the checker cannot reorder the payload. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

/-- PageBatchWitness is reused as a container; its index and page denote a block here. -/
def executeBlockBatches (block : Nat) : St → List PageBatchWitness → St
  | s, [] => s
  | s, w :: ws => executeBlockBatches block
      (executeByteRequests s (blockBatchRequests block w.index w.writes)) ws

def checkBlockBatches (hash : Bytes → ByteArray) : BlockDescriptor → List PageBatchWitness → Option BlockDescriptor
  | d, [] => some d
  | d, w :: ws => (checkBlockBatch hash d w.index w.page w.path w.writes).bind
      (fun next => checkBlockBatches hash next ws)

def blockBatchCollision (hash : Bytes → ByteArray) (block count depth : Nat) : St → List PageBatchWitness → Prop
  | _, [] => False
  | s, w :: ws =>
    PageCollisionIn hash
      ((pageTreeMessages (blockTreeHash hash block) (buildSubpageTree s block count depth)).map (blockHashMessage block))
      ((pageOpeningMessages (blockTreeHash hash block) w.page w.path).map (blockHashMessage block)) ∨
    blockBatchCollision hash block count depth
      (executeByteRequests s (blockBatchRequests block w.index w.writes)) ws

theorem checked_block_batch_chain (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (block count depth : Nat)
    (s : St) (full : fullPages s.pages) (ws : List PageBatchWitness) (output : BlockDescriptor)
    (accepted : checkBlockBatches hash (describeSubpageMemory hash s block count depth) ws = some output) :
    output = describeSubpageMemory hash (executeBlockBatches block s ws) block count depth ∨
      blockBatchCollision hash block count depth s ws := by
  induction ws generalizing s output with
  | nil => exact Or.inl (Option.some.inj accepted).symm
  | cons w ws ih =>
    cases he : checkBlockBatch hash (describeSubpageMemory hash s block count depth) w.index w.page w.path w.writes with
    | none => simp [checkBlockBatches, he] at accepted
    | some next =>
      rcases checked_block_batch_correct_or_collision hash digestBound s full block count depth w.index
        w.page w.path w.writes next he with hn | hc
      · simp only [checkBlockBatches, he, Option.bind_some, hn] at accepted
        rcases ih _ (execute_requests_full_pages s full _) output accepted with hout | hcollision
        · exact Or.inl hout
        · exact Or.inr (Or.inr hcollision)
      · exact Or.inr (Or.inl hc)

def blockBatchSequenceRequests (block : Nat) : List PageBatchWitness → List (Nat × UInt8)
  | [] => []
  | w :: ws => blockBatchRequests block w.index w.writes ++ blockBatchSequenceRequests block ws

theorem execute_block_batches_requests (block : Nat) (s : St) (ws : List PageBatchWitness) :
    executeBlockBatches block s ws = executeByteRequests s (blockBatchSequenceRequests block ws) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    simp only [executeBlockBatches, blockBatchSequenceRequests, executeByteRequests, List.foldl_append] at *
    exact ih _

def checkBlockBatchedWriteBytes (hash : Bytes → ByteArray) (initial : BlockDescriptor)
    (address : Nat) (data : ByteArray) (ws : List PageBatchWitness) : Option BlockDescriptor :=
  if blockBatchSequenceRequests initial.block ws = byteWriteRequests address data then
    checkBlockBatches hash initial ws
  else none

theorem checked_block_batched_write_bytes_correct_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (block count depth : Nat)
    (s : St) (full : fullPages s.pages) (address : Nat) (data : ByteArray)
    (ws : List PageBatchWitness) (output : BlockDescriptor)
    (accepted : checkBlockBatchedWriteBytes hash (describeSubpageMemory hash s block count depth)
      address data ws = some output) :
    output = describeSubpageMemory hash (writeBytes s address data) block count depth ∨
      blockBatchCollision hash block count depth s ws := by
  unfold checkBlockBatchedWriteBytes at accepted
  split at accepted
  · rename_i requests
    change blockBatchSequenceRequests block ws = byteWriteRequests address data at requests
    rcases checked_block_batch_chain hash digestBound block count depth s full ws output accepted with he | hc
    · rw [execute_block_batches_requests, requests, ← write_bytes_requests_exact] at he
      exact Or.inl he
    · exact Or.inr hc
  · contradiction

theorem check_block_batched_bytes_rejects_wrong_requests (hash : Bytes → ByteArray)
    (initial : BlockDescriptor) (address : Nat) (data : ByteArray) (ws : List PageBatchWitness)
    (different : blockBatchSequenceRequests initial.block ws ≠ byteWriteRequests address data) :
    checkBlockBatchedWriteBytes hash initial address data ws = none := by
  simp [checkBlockBatchedWriteBytes, different]

end NearCompression
