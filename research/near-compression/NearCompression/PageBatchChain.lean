import NearCompression.PageBatch

/-! Ordered multi-page batch composition, with exact writeBytes request binding.
Witness grouping is supplied; no cross-operation reordering is permitted. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

structure PageBatchWitness where
  index : Nat
  page : ByteArray
  path : List (Bool × ByteArray)
  writes : List (Nat × UInt8)

def pageBatchWitnessWf (w : PageBatchWitness) : Prop := bytesWireWf w.page ∧ pageOpeningWf w.path

def executePageBatches : St → List PageBatchWitness → St
  | s, [] => s
  | s, w :: ws => executePageBatches (executeByteRequests s (pageBatchRequests w.index w.writes)) ws

def checkPageBatches (hash : Bytes → ByteArray) : MemoryDescriptor → List PageBatchWitness → Option MemoryDescriptor
  | d, [] => some d
  | d, w :: ws => (checkPageBatch hash d w.index w.page w.path w.writes).bind
      (fun next => checkPageBatches hash next ws)

def pageBatchCollision (hash : Bytes → ByteArray) (depth : Nat) : St → List PageBatchWitness → Prop
  | _, [] => False
  | s, w :: ws =>
    PageCollisionIn hash (pageTreeMessages hash (buildPageTree s.pages depth 0))
      (pageOpeningMessages hash w.page w.path) ∨
    pageBatchCollision hash depth (executeByteRequests s (pageBatchRequests w.index w.writes)) ws

theorem execute_byte_requests_pages_wf (s : St) (wf : memoryPagesWf s) (requests : List (Nat × UInt8)) :
    memoryPagesWf (executeByteRequests s requests) := by
  induction requests generalizing s with
  | nil => exact wf
  | cons r rs ih => exact ih _ (write_byte_pages_wf s wf r.1 r.2)

theorem checked_page_batch_chain (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (depth : Nat)
    (s : St) (pagesWf : memoryPagesWf s) (ws : List PageBatchWitness)
    (witnessWf : ∀ w ∈ ws, pageBatchWitnessWf w) (output : MemoryDescriptor)
    (accepted : checkPageBatches hash (describeMemory hash s depth) ws = some output) :
    output = describeMemory hash (executePageBatches s ws) depth ∨ pageBatchCollision hash depth s ws := by
  induction ws generalizing s output with
  | nil => exact Or.inl (Option.some.inj accepted).symm
  | cons w ws ih =>
    have hw := witnessWf w (by simp)
    cases he : checkPageBatch hash (describeMemory hash s depth) w.index w.page w.path w.writes with
    | none => simp [checkPageBatches, he] at accepted
    | some next =>
      rcases checked_page_batch_correct_or_collision hash digestBound s depth w.index pagesWf
        w.page hw.1 w.path hw.2 w.writes next he with hn | hc
      · simp only [checkPageBatches, he, Option.bind_some, hn] at accepted
        rcases ih _ (execute_byte_requests_pages_wf s pagesWf _) (fun v hv => witnessWf v (by simp [hv]))
          output accepted with hout | hcollision
        · exact Or.inl hout
        · exact Or.inr (Or.inr hcollision)
      · exact Or.inr (Or.inl hc)

def pageBatchSequenceRequests : List PageBatchWitness → List (Nat × UInt8)
  | [] => []
  | w :: ws => pageBatchRequests w.index w.writes ++ pageBatchSequenceRequests ws

theorem execute_page_batches_requests (s : St) (ws : List PageBatchWitness) :
    executePageBatches s ws = executeByteRequests s (pageBatchSequenceRequests ws) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    simp only [executePageBatches, pageBatchSequenceRequests, executeByteRequests, List.foldl_append] at *
    exact ih _

def checkBatchedWriteBytes (hash : Bytes → ByteArray) (initial : MemoryDescriptor)
    (address : Nat) (data : ByteArray) (ws : List PageBatchWitness) : Option MemoryDescriptor :=
  if pageBatchSequenceRequests ws = byteWriteRequests address data then
    checkPageBatches hash initial ws
  else none

theorem checked_batched_write_bytes_correct_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (depth : Nat)
    (s : St) (pagesWf : memoryPagesWf s) (address : Nat) (data : ByteArray)
    (ws : List PageBatchWitness) (witnessWf : ∀ w ∈ ws, pageBatchWitnessWf w)
    (output : MemoryDescriptor)
    (accepted : checkBatchedWriteBytes hash (describeMemory hash s depth) address data ws = some output) :
    output = describeMemory hash (writeBytes s address data) depth ∨ pageBatchCollision hash depth s ws := by
  unfold checkBatchedWriteBytes at accepted
  split at accepted
  · rename_i requests
    rcases checked_page_batch_chain hash digestBound depth s pagesWf ws witnessWf output accepted with he | hc
    · rw [execute_page_batches_requests, requests, ← write_bytes_requests_exact] at he
      exact Or.inl he
    · exact Or.inr hc
  · contradiction

end NearCompression
