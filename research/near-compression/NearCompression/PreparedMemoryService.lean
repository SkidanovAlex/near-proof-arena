import NearCompression.PreparedMemoryRead
import NearCompression.BlockWriteChain
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

inductive PreparedMemoryAction where
  | read (value : Nat) (openings : List PreparedMemoryReadOpening)
  | write (value : Nat) (batches : List PageBatchWitness)

/-- Ordered scalar service request. Execution-bus authentication of this
clock and payload remains a separate obligation. -/
structure PreparedMemoryRequest where
  clock : Nat
  address : Nat
  width : Nat
  action : PreparedMemoryAction

def preparedMemoryServiceCheck (hash : Bytes→ByteArray) :
    BlockDescriptor→Nat→List PreparedMemoryRequest→Option BlockDescriptor
  | d,_,[]=>some d
  | d,clock,q::qs=>
    if q.clock=clock then
      match q.action with
      | .read value openings=>
        if preparedMemoryReadCheck hash d q.address q.width openings &&
            decide (value=preparedMemoryReadValue d q.address q.width openings) then
          preparedMemoryServiceCheck hash d (clock+1) qs
        else none
      | .write value batches=>
        (preparedScalarStoreCheck hash d q.address q.width value batches).bind
          (fun next=>preparedMemoryServiceCheck hash next (clock+1) qs)
    else none

def preparedMemoryServiceExec : St→List PreparedMemoryRequest→St
  | s,[]=>s
  | s,q::qs=>match q.action with
    | .read _ _=>preparedMemoryServiceExec s qs
    | .write value _=>preparedMemoryServiceExec (writeLE s q.address q.width value) qs

/-- Each read is evaluated at its actual intermediate state, after all earlier
writes and before all later writes. -/
def PreparedMemoryServiceReads : St→List PreparedMemoryRequest→Prop
  | _,[]=>True
  | s,q::qs=>match q.action with
    | .read value _=>value=readLE s q.address q.width ∧ PreparedMemoryServiceReads s qs
    | .write value _=>PreparedMemoryServiceReads (writeLE s q.address q.width value) qs

/-- Finite supported collision alternatives retain the intermediate state's
actual tree and the submitted read opening or write batch. -/
def PreparedMemoryServiceCollision (hash : Bytes→ByteArray) (block count depth : Nat) :
    St→List PreparedMemoryRequest→Prop
  | _,[]=>False
  | s,q::qs=>match q.action with
    | .read _ openings=>PreparedMemoryReadCollision hash s block count depth q.width openings ∨
        PreparedMemoryServiceCollision hash block count depth s qs
    | .write value batches=>blockBatchCollision hash block count depth s batches ∨
        PreparedMemoryServiceCollision hash block count depth (writeLE s q.address q.width value) qs

theorem prepared_memory_mixed_clocks (hash : Bytes→ByteArray) (d : BlockDescriptor)
    (clock : Nat) (requests : List PreparedMemoryRequest) (output : BlockDescriptor)
    (accepted : preparedMemoryServiceCheck hash d clock requests=some output) :
    requests.map PreparedMemoryRequest.clock=List.range' clock requests.length := by
  induction requests generalizing d clock with
  | nil=>rfl
  | cons q qs ih=>
    simp only [preparedMemoryServiceCheck] at accepted
    split at accepted
    · rename_i time
      have tail : qs.map PreparedMemoryRequest.clock=List.range' (clock+1) qs.length := by
        cases act : q.action with
        | read value openings=>
          simp only [act] at accepted
          split at accepted
          · exact ih d (clock+1) accepted
          · cases accepted
        | write value batches=>
          simp only [act] at accepted
          cases checked : preparedScalarStoreCheck hash d q.address q.width value batches with
          | none=>simp only [checked,Option.bind_none] at accepted;cases accepted
          | some next=>
            simp only [checked,Option.bind_some] at accepted
            exact ih next (clock+1) accepted
      simp only [List.map_cons,List.length_cons,List.range'_succ,time,tail]
    · cases accepted

/-- Checker acceptance derives both final-root correctness and every read's
value at its exact intermediate root, or a finitely supported hash collision.
This is a service checker theorem, not a MEM AIR or bus-ordering theorem. -/
theorem prepared_memory_mixed_checked (hash : Bytes→ByteArray)
    (digestBound : ∀bs,bytesWireWf (hash bs)) (block count depth : Nat)
    (s : St) (full : fullPages s.pages)
    (referenceWf : blockDescriptorWf (describeSubpageMemory hash s block count depth))
    (clock : Nat) (requests : List PreparedMemoryRequest) (output : BlockDescriptor)
    (accepted : preparedMemoryServiceCheck hash (describeSubpageMemory hash s block count depth)
      clock requests=some output) :
    (output=describeSubpageMemory hash (preparedMemoryServiceExec s requests) block count depth ∧
      PreparedMemoryServiceReads s requests) ∨
      PreparedMemoryServiceCollision hash block count depth s requests := by
  induction requests generalizing s clock with
  | nil=>exact Or.inl ⟨(Option.some.inj accepted).symm,True.intro⟩
  | cons q qs ih=>
    simp only [preparedMemoryServiceCheck] at accepted
    split at accepted
    · cases act : q.action with
      | read value openings=>
        simp only [act] at accepted
        split at accepted
        · rename_i checks
          have checks' := checks
          simp only [Bool.and_eq_true,decide_eq_true_eq] at checks'
          obtain ⟨_,_,_,readResult⟩:=prepared_memory_read_checked hash digestBound s full
            block count depth q.address q.width referenceWf openings checks'.1
          rcases readResult with correct|bad
          · rcases ih s full referenceWf (clock+1) accepted with success|bad
            · exact Or.inl ⟨by simpa only [preparedMemoryServiceExec,act] using success.1,
                by simpa only [PreparedMemoryServiceReads,act] using
                  And.intro (checks'.2.trans correct.symm) success.2⟩
            · exact Or.inr (by simpa only [PreparedMemoryServiceCollision,act] using Or.inr bad)
          · exact Or.inr (by simpa only [PreparedMemoryServiceCollision,act] using Or.inl bad)
        · cases accepted
      | write value batches=>
        simp only [act] at accepted
        cases checked : preparedScalarStoreCheck hash (describeSubpageMemory hash s block count depth)
            q.address q.width value batches with
        | none=>simp only [checked,Option.bind_none] at accepted;cases accepted
        | some next=>
          simp only [checked,Option.bind_some] at accepted
          obtain ⟨_,_,result⟩:=prepared_scalar_store_checked hash digestBound block count depth s full
            q.address q.width value batches next checked
          rcases result with correct|bad
          · rw [correct] at accepted
            have pages : (writeLE s q.address q.width value).pages.size=s.pages.size := by
              rw [prepared_scalar_write_exact]
              exact execute_byte_requests_page_count _ _
            have nextWf := describe_subpage_memory_wf hash digestBound
              (writeLE s q.address q.width value) block count depth referenceWf.1 referenceWf.2.1
              (by simpa only [pages,describeSubpageMemory] using referenceWf.2.2.1) referenceWf.2.2.2.1
            rcases ih _ (write_le_full_pages s full q.address q.width value) nextWf
                (clock+1) accepted with success|bad
            · exact Or.inl (by simpa only [preparedMemoryServiceExec,PreparedMemoryServiceReads,act] using success)
            · exact Or.inr (by simpa only [PreparedMemoryServiceCollision,act] using Or.inr bad)
          · exact Or.inr (by simpa only [PreparedMemoryServiceCollision,act] using Or.inl bad)
    · cases accepted
end NearCompression
