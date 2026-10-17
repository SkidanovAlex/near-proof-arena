import NearCompression.MemoryHostPhases

/-! Projected host verification: exact gas, terminal error and memory descriptor.
Other state fields and initial commitment authentication belong to the enclosing relation. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def memoryHostView (hash : Bytes → ByteArray) (block count depth : Nat) :
    EStateM.Result String St Unit → EStateM.Result String (Gas × BlockDescriptor) Unit
  | .ok _ s => .ok () (s.gas, describeSubpageMemory hash s block count depth)
  | .error e s => .error e (s.gas, describeSubpageMemory hash s block count depth)

def checkMemoryHostWrite (hash : Bytes → ByteArray) (base byte : Cost) (gas : Gas)
    (d : BlockDescriptor) (address : Nat) (data : ByteArray) (ws : List PageBatchWitness) :
    Option (EStateM.Result String (Gas × BlockDescriptor) Unit) :=
  let charged := memoryWriteCharges base byte data.size gas
  match charged.2 with
  | some error => some (.error error (charged.1, d))
  | none => if address + data.size > d.pages * pageSize then
      some (.error "HostError(MemoryAccessViolation)" (charged.1, d))
    else (checkBlockBatchedWriteBytes hash d address data ws).map (fun next => .ok () (charged.1, next))

theorem byte_requests_preserve_gas (s : St) (requests : List (Nat × UInt8)) :
    (executeByteRequests s requests).gas = s.gas := by
  induction requests generalizing s with
  | nil => rfl
  | cons r rs ih => exact ih (writeByte s r.1 r.2)

theorem write_bytes_preserve_gas (s : St) (address : Nat) (data : ByteArray) :
    (writeBytes s address data).gas = s.gas := by
  rw [write_bytes_requests_exact]
  exact byte_requests_preserve_gas s _

theorem checked_memory_host_phases (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (base byte : Cost)
    (s : St) (full : fullPages s.pages) (block count depth address : Nat)
    (data : ByteArray) (ws : List PageBatchWitness)
    (output : EStateM.Result String (Gas × BlockDescriptor) Unit)
    (accepted : checkMemoryHostWrite hash base byte s.gas (describeSubpageMemory hash s block count depth)
      address data ws = some output) :
    output = memoryHostView hash block count depth (memoryWritePhases base byte s address data) ∨
    blockBatchCollision hash block count depth
      { s with gas := (memoryWriteCharges base byte data.size s.gas).1 } ws := by
  let charged := memoryWriteCharges base byte data.size s.gas
  let t := { s with gas := charged.1 }
  have descriptor : describeSubpageMemory hash t block count depth = describeSubpageMemory hash s block count depth := rfl
  cases he : (memoryWriteCharges base byte data.size s.gas).2 with
  | some error =>
    apply Or.inl
    have ha : some (EStateM.Result.error error (charged.1, describeSubpageMemory hash s block count depth)) = some output := by
      simpa only [checkMemoryHostWrite, he] using accepted
    rw [← Option.some.inj ha]
    simp only [memoryWritePhases, he, memoryHostView]
    rfl
  | none =>
    by_cases hb : address + data.size > s.pages.size * pageSize
    · apply Or.inl
      have ha : some (EStateM.Result.error "HostError(MemoryAccessViolation)"
          (charged.1, describeSubpageMemory hash s block count depth)) = some output := by
        simpa only [checkMemoryHostWrite, he, describeSubpageMemory, hb, ite_true] using accepted
      rw [← Option.some.inj ha]
      simp only [memoryWritePhases, he, memBytes, hb, ite_true, memoryHostView]
      rfl
    · have ha : (checkBlockBatchedWriteBytes hash (describeSubpageMemory hash t block count depth) address data ws).map
          (fun next => EStateM.Result.ok () (charged.1, next)) = some output := by
        rw [descriptor]
        simpa only [checkMemoryHostWrite, he, describeSubpageMemory, hb, ite_false] using accepted
      cases hc : checkBlockBatchedWriteBytes hash (describeSubpageMemory hash t block count depth) address data ws with
      | none => simp [hc] at ha
      | some next =>
        have ho : EStateM.Result.ok () (charged.1, next) = output := by simpa [hc] using ha
        rcases checked_block_batched_write_bytes_correct_or_collision hash digestBound block count depth t full
          address data ws next hc with correct | collision
        · apply Or.inl
          rw [← ho, correct]
          simp only [memoryWritePhases,   he, memBytes, hb, ite_false, memoryHostView, write_bytes_preserve_gas]
          rfl
        · exact Or.inr collision

theorem checked_actual_memory_host (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (s : St) (full : fullPages s.pages)
    (block count depth address : Nat) (data : ByteArray) (ws : List PageBatchWitness)
    (output : EStateM.Result String (Gas × BlockDescriptor) Unit)
    (accepted : checkMemoryHostWrite hash C.writeMemoryBase C.writeMemoryByte s.gas
      (describeSubpageMemory hash s block count depth) address data ws = some output) :
    output = memoryHostView hash block count depth ((writeMemH address data).run s) ∨
    blockBatchCollision hash block count depth
      { s with gas := (memoryWriteCharges C.writeMemoryBase C.writeMemoryByte data.size s.gas).1 } ws := by
  rw [actual_memory_write_phases]
  with_reducible exact checked_memory_host_phases hash digestBound C.writeMemoryBase C.writeMemoryByte s full block count depth address data ws output accepted

end NearCompression
