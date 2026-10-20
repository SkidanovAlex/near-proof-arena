import NearCompression.PreparedMemoryScalar
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

/-- One scalar write request. Clock must come from the execution event bus;
the service checks consecutive order and chains every intermediate root. -/
structure PreparedMemoryStoreRequest where
  clock : Nat
  address : Nat
  width : Nat
  value : Nat
  batches : List PageBatchWitness

def preparedMemoryStoreServiceCheck (hash : Bytes→ByteArray) :
    BlockDescriptor→Nat→List PreparedMemoryStoreRequest→Option BlockDescriptor
  | d,_,[]=>some d
  | d,clock,w::ws=>
    if w.clock=clock then
      (preparedScalarStoreCheck hash d w.address w.width w.value w.batches).bind
        (fun next=>preparedMemoryStoreServiceCheck hash next (clock+1) ws)
    else none

def preparedMemoryStoreServiceExec : St→List PreparedMemoryStoreRequest→St
  | s,[]=>s
  | s,w::ws=>preparedMemoryStoreServiceExec (writeLE s w.address w.width w.value) ws

def PreparedMemoryStoreServiceCollision (hash : Bytes→ByteArray) (block count depth : Nat) :
    St→List PreparedMemoryStoreRequest→Prop
  | _,[]=>False
  | s,w::ws=>blockBatchCollision hash block count depth s w.batches ∨
      PreparedMemoryStoreServiceCollision hash block count depth (writeLE s w.address w.width w.value) ws

/-- Clock checks are independent of hash assumptions and prevent skipping,
repeating or reordering the supplied service requests. Authentication of
these clocks/messages by the execution bus remains separate. -/
theorem prepared_memory_service_clocks (hash : Bytes→ByteArray) (d : BlockDescriptor)
    (clock : Nat) (requests : List PreparedMemoryStoreRequest) (output : BlockDescriptor)
    (accepted : preparedMemoryStoreServiceCheck hash d clock requests=some output) :
    requests.map PreparedMemoryStoreRequest.clock=List.range' clock requests.length := by
  induction requests generalizing d clock with
  | nil=>rfl
  | cons w ws ih=>
    simp only [preparedMemoryStoreServiceCheck] at accepted
    split at accepted
    · rename_i time
      cases checked : preparedScalarStoreCheck hash d w.address w.width w.value w.batches with
      | none=>simp only [checked,Option.bind_none] at accepted;cases accepted
      | some next=>
        simp only [checked,Option.bind_some] at accepted
        simp only [List.map_cons,List.length_cons,List.range'_succ,time]
        exact congrArg (List.cons clock) (ih next (clock+1) accepted)
    · cases accepted

/-- Every accepted root transition refines the next actual scalar write,
with a collision supported by the exact intermediate state's queried tree
and supplied opening. No arbitrary permutation of memory events is assumed. -/
theorem prepared_memory_service_checked (hash : Bytes→ByteArray)
    (digestBound : ∀bs,bytesWireWf (hash bs)) (block count depth : Nat)
    (s : St) (full : fullPages s.pages) (clock : Nat)
    (requests : List PreparedMemoryStoreRequest) (output : BlockDescriptor)
    (accepted : preparedMemoryStoreServiceCheck hash (describeSubpageMemory hash s block count depth)
      clock requests=some output) :
    output=describeSubpageMemory hash (preparedMemoryStoreServiceExec s requests) block count depth ∨
      PreparedMemoryStoreServiceCollision hash block count depth s requests := by
  induction requests generalizing s clock with
  | nil=>exact Or.inl (Option.some.inj accepted).symm
  | cons w ws ih=>
    simp only [preparedMemoryStoreServiceCheck] at accepted
    split at accepted
    · cases checked : preparedScalarStoreCheck hash (describeSubpageMemory hash s block count depth)
          w.address w.width w.value w.batches with
      | none=>simp only [checked,Option.bind_none] at accepted;cases accepted
      | some next=>
        simp only [checked,Option.bind_some] at accepted
        obtain ⟨_,_,result⟩:=prepared_scalar_store_checked hash digestBound block count depth s full
          w.address w.width w.value w.batches next checked
        rcases result with correct|collision
        · rw [correct] at accepted
          rcases ih _ (write_le_full_pages s full w.address w.width w.value) (clock+1) accepted with success|bad
          · exact Or.inl success
          · exact Or.inr (Or.inr bad)
        · exact Or.inr (Or.inl collision)
    · cases accepted
end NearCompression
