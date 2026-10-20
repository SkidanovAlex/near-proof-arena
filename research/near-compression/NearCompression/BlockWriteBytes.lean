import NearCompression.BlockWriteChain

/-! Bind checked block writes to the actual writeBytes loop, with executable
witness encoding-bound checks. This is not the enclosing host bounds/gas check. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def checkWriteWitnessWf (w : MemoryWriteWitness) : Bool :=
  decide (w.page.size < 4294967296) &&
    w.path.all (fun x => decide (x.2.size < 4294967296))

theorem check_write_witness_wf_correct (w : MemoryWriteWitness) :
    checkWriteWitnessWf w = true ↔ memoryWriteWitnessWf w := by
  simp [checkWriteWitnessWf, memoryWriteWitnessWf, pageOpeningWf, bytesWireWf,
    ByteArray.size_data]

def checkBlockWriteBytes (hash : Bytes → ByteArray) (initial : BlockDescriptor)
    (address : Nat) (data : ByteArray) (ws : List MemoryWriteWitness) : Option BlockDescriptor :=
  if ws.all checkWriteWitnessWf && decide (memoryWitnessRequests ws = byteWriteRequests address data) then
    checkBlockWrites hash initial ws
  else none

theorem checked_block_write_bytes_correct_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (block count depth : Nat)
    (blockBound : nat128WireWf block) (countBound : nat128WireWf count) (depthBound : nat128WireWf depth)
    (s : St) (full : fullPages s.pages) (pagesBound : nat128WireWf s.pages.size)
    (address : Nat) (data : ByteArray) (ws : List MemoryWriteWitness) (output : BlockDescriptor)
    (accepted : checkBlockWriteBytes hash (describeSubpageMemory hash s block count depth)
      address data ws = some output) :
    output = describeSubpageMemory hash (writeBytes s address data) block count depth ∨
      blockWriteCollision hash block count depth s ws := by
  unfold checkBlockWriteBytes at accepted
  split at accepted
  · rename_i checks
    have checks' : (∀ w ∈ ws, memoryWriteWitnessWf w) ∧
        memoryWitnessRequests ws = byteWriteRequests address data := by
      simpa only [Bool.and_eq_true, List.all_eq_true, check_write_witness_wf_correct,
        decide_eq_true_eq] using checks
    rcases checked_block_write_chain hash digestBound block count depth blockBound countBound depthBound
      s full pagesBound ws checks'.1 output accepted with correct | collision
    · exact Or.inl ((write_bytes_witness_exact s address data ws checks'.2) ▸ correct)
    · exact Or.inr collision
  · contradiction

/-- Witnesses with a different ordered request stream are rejected before tree checking. -/
theorem check_block_write_bytes_rejects_wrong_requests (hash : Bytes → ByteArray)
    (initial : BlockDescriptor) (address : Nat) (data : ByteArray) (ws : List MemoryWriteWitness)
    (different : memoryWitnessRequests ws ≠ byteWriteRequests address data) :
    checkBlockWriteBytes hash initial address data ws = none := by
  simp [checkBlockWriteBytes, different]

end NearCompression
