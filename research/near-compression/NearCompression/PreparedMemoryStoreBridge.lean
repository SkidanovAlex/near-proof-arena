import NearCompression.PreparedMemoryLoadService
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def preparedMemoryStoreValue (row : Nat→Fp) (selected : Nat) : Val :=
  if preparedMemoryIs64 selected then .i64 (UInt64.ofNat (preparedMemoryWord row 229))
  else .i32 (UInt32.ofNat (preparedMemoryWord row 229))
def preparedMemoryStoreRequest (row : Nat→Fp) (selected : Nat)
    (batches : List PageBatchWitness) : PreparedMemoryRequest :=
  ⟨preparedMemoryWord row 51,preparedMemoryEffectiveAddress row,preparedMemoryWidth selected,
    .write (preparedMemoryWord row 293) batches⟩

theorem prepared_memory_store_exec_row
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedMemoryLiteralTable tr t pub) (hr:r<tr.height t)
    (selected : Fin 19) (hot:∀i,i<19→tr.cell t r i=if i=selected.val then 1 else 0)
    (store:12≤selected.val) (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (pf : PFunc) (align : Nat)
    (bounds:preparedMemoryEffectiveAddress (tr.cell t r)+preparedMemoryWidth selected≤memBytes s) :
    exec cfg p (pushV (pushV s (.i32 (UInt32.ofNat (preparedMemoryAddressWord (tr.cell t r) 115))))
        (preparedMemoryStoreValue (tr.cell t r) selected)) f pf
      (.store (preparedMemoryOpcode selected) align (preparedMemoryAddressWord (tr.cell t r) 147))=
      .cont (setFrame (writeLE s (preparedMemoryEffectiveAddress (tr.cell t r))
        (preparedMemoryWidth selected) (preparedMemoryWord (tr.cell t r) 293)) {f with pc:=f.pc+1}) := by
  have source:=prepared_memory_literal_bounds tr t r pub localH hr
  have addr:=prepared_memory_address_uint32 (tr.cell t r) source.1 115 (by decide)
  have ea:=prepared_memory_address_exact (tr.cell t r) source.1
  change preparedMemoryEffectiveAddress (tr.cell t r)=_ at ea
  have raw:=prepared_memory_store_word tr t r pub localH hr selected hot store
  have widths : ∀i:Fin 19,12≤i.val→storeWidth (preparedMemoryOpcode i)=preparedMemoryWidth i := by decide
  have width:=widths selected store
  have divisors : ∀i:Fin 19,12≤i.val→
      256^(storeWidth (preparedMemoryOpcode i))∣(if preparedMemoryIs64 i then 18446744073709551616 else 4294967296) := by decide
  have dvd:=divisors selected store
  unfold preparedMemoryStoreValue
  cases tag:preparedMemoryIs64 selected
  · simp only [tag,Bool.false_eq_true,ite_false] at dvd ⊢
    rw [prepared_memory_store_i32_exec,addr,←ea]
    have narrowed : (UInt32.ofNat (preparedMemoryWord (tr.cell t r) 229)).toNat%
        256^(storeWidth (preparedMemoryOpcode selected))=preparedMemoryWord (tr.cell t r) 293 := by
      change preparedMemoryWord (tr.cell t r) 229%4294967296%_= _
      rw [Nat.mod_mod_of_dvd _ dvd,←raw]
    rw [narrowed,width,ite_eq_right (by omega),←prepared_scalar_write_exact]
  · simp only [tag,ite_true] at dvd ⊢
    rw [prepared_memory_store_i64_exec,addr,←ea]
    have narrowed : (UInt64.ofNat (preparedMemoryWord (tr.cell t r) 229)).toNat%
        256^(storeWidth (preparedMemoryOpcode selected))=preparedMemoryWord (tr.cell t r) 293 := by
      change preparedMemoryWord (tr.cell t r) 229%18446744073709551616%_= _
      rw [Nat.mod_mod_of_dvd _ dvd,←raw]
    rw [narrowed,width,ite_eq_right (by omega),←prepared_scalar_write_exact]

/-- Accepted decoded write requests refine the exact actual store and its
post-pop stack/PC. Each collision remains supported at this actual memory root. -/
theorem prepared_memory_store_service_exec
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedMemoryLiteralTable tr t pub) (hr:r<tr.height t)
    (selected : Fin 19) (hot:∀i,i<19→tr.cell t r i=if i=selected.val then 1 else 0)
    (store:12≤selected.val) (hash : Bytes→ByteArray) (digestBound:∀bs,bytesWireWf (hash bs))
    (cfg : NearCfg) (p : Prepared) (s : St) (full:fullPages s.pages)
    (block count depth : Nat) (f : Frame) (pf : PFunc) (align : Nat)
    (batches : List PageBatchWitness) (output : BlockDescriptor)
    (accepted : preparedMemoryServiceCheck hash (describeSubpageMemory hash s block count depth)
      (preparedMemoryWord (tr.cell t r) 51) [preparedMemoryStoreRequest (tr.cell t r) selected batches]=some output) :
    (∃next,exec cfg p (pushV (pushV s (.i32 (UInt32.ofNat (preparedMemoryAddressWord (tr.cell t r) 115))))
          (preparedMemoryStoreValue (tr.cell t r) selected)) f pf
        (.store (preparedMemoryOpcode selected) align (preparedMemoryAddressWord (tr.cell t r) 147))=.cont next ∧
        output=describeSubpageMemory hash next block count depth) ∨
      blockBatchCollision hash block count depth s batches := by
  simp only [preparedMemoryServiceCheck,preparedMemoryStoreRequest,ite_true,Option.bind_fun_some] at accepted
  have checked : preparedScalarStoreCheck hash (describeSubpageMemory hash s block count depth)
      (preparedMemoryEffectiveAddress (tr.cell t r)) (preparedMemoryWidth selected)
      (preparedMemoryWord (tr.cell t r) 293) batches=some output := accepted
  obtain ⟨_,bounds,result⟩:=prepared_scalar_store_checked hash digestBound block count depth s full _ _ _ batches output checked
  rcases result with correct|collision
  · apply Or.inl
    refine ⟨setFrame (writeLE s (preparedMemoryEffectiveAddress (tr.cell t r))
      (preparedMemoryWidth selected) (preparedMemoryWord (tr.cell t r) 293)) {f with pc:=f.pc+1},?_,?_⟩
    · exact prepared_memory_store_exec_row tr t r pub localH hr selected hot store cfg p s f pf align bounds
    · unfold setFrame
      split <;> exact correct
  · exact Or.inr collision
end NearCompression
