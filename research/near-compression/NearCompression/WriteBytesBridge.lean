import NearCompression.MemoryWriteChain

/-! Connect checked write witnesses to the actual dependent-index writeBytes loop. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def byteWriteRequests (address : Nat) (data : ByteArray) : List (Nat × UInt8) :=
  (List.range' 0 data.size).map (fun i => (address + i, data[i]!))

def executeByteRequests (s : St) (requests : List (Nat × UInt8)) : St :=
  requests.foldl (fun st r => writeByte st r.1 r.2) s

theorem for_in_bytes_fold (data : ByteArray) (address : Nat) (xs : List Nat)
    (bound : ∀ i ∈ xs, i < data.size) (s : St) :
    (forIn' (m := Id) xs s fun i hi st =>
      ForInStep.yield (writeByte st (address + i) (data[i]'(bound i hi)))) =
      xs.foldl (fun st i => writeByte st (address + i) data[i]!) s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn'_cons, List.foldl_cons]
    rw [getElem!_pos data x (bound x (by simp))]
    exact ih (fun i hi => bound i (by simp [hi])) _

theorem write_bytes_requests_exact (s : St) (address : Nat) (data : ByteArray) :
    writeBytes s address data = executeByteRequests s (byteWriteRequests address data) := by
  unfold writeBytes executeByteRequests byteWriteRequests
  simp only [Id.run, Std.Legacy.Range.forIn'_eq_forIn'_range', List.foldl_map]
  simpa [Std.Legacy.Range.size, bind, pure] using
    for_in_bytes_fold data address (List.range' 0 data.size)
      (by intro i hi; simpa [List.mem_range'] using hi) s

def memoryWitnessRequests (ws : List MemoryWriteWitness) : List (Nat × UInt8) :=
  ws.map (fun w => (w.address, w.value))

theorem execute_memory_witness_requests (s : St) (ws : List MemoryWriteWitness) :
    executeMemoryWrites s ws = executeByteRequests s (memoryWitnessRequests ws) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    simpa only [executeMemoryWrites, executeByteRequests, memoryWitnessRequests,
      List.map_cons, List.foldl_cons] using ih (writeByte s w.address w.value)

theorem write_bytes_witness_exact (s : St) (address : Nat) (data : ByteArray)
    (ws : List MemoryWriteWitness)
    (requests : memoryWitnessRequests ws = byteWriteRequests address data) :
    executeMemoryWrites s ws = writeBytes s address data := by
  rw [execute_memory_witness_requests, requests, write_bytes_requests_exact]

def checkWriteBytes (hash : Bytes → ByteArray) (initial : MemoryDescriptor)
    (address : Nat) (data : ByteArray) (ws : List MemoryWriteWitness) : Option MemoryDescriptor :=
  if memoryWitnessRequests ws = byteWriteRequests address data then
    checkMemoryWrites hash initial ws
  else none

theorem checked_write_bytes_correct_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (depth : Nat) (depthBound : nat128WireWf depth)
    (s : St) (pagesWf : memoryPagesWf s) (countBound : nat128WireWf s.pages.size)
    (address : Nat) (data : ByteArray) (ws : List MemoryWriteWitness)
    (witnessWf : ∀ w ∈ ws, memoryWriteWitnessWf w) (output : MemoryDescriptor)
    (accepted : checkWriteBytes hash (describeMemory hash s depth) address data ws = some output) :
    output = describeMemory hash (writeBytes s address data) depth ∨ memoryWriteCollision hash depth s ws := by
  unfold checkWriteBytes at accepted
  split at accepted
  · rename_i requests
    rcases checked_memory_write_chain hash digestBound depth depthBound s pagesWf countBound
      ws witnessWf output accepted with he | hc
    · exact Or.inl ((write_bytes_witness_exact s address data ws requests) ▸ he)
    · exact Or.inr hc
  · contradiction

end NearCompression
