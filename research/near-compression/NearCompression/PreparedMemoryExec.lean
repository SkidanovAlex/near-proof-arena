import NearCompression.PreparedMemoryScalar
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

/-- Result extension/tagging is exactly the interpreter's loadSpec. Legal
opcode and alignment validation belong to authenticated preparation. -/
def preparedMemoryLoadedValue (op value : Nat) : Val :=
  let (width,signed,is64):=loadSpec op
  let extended:=if signed then Num.extendS (if is64 then 64 else 32) (8*width) value else value
  if is64 then .i64 (UInt64.ofNat extended) else .i32 (UInt32.ofNat extended)

theorem prepared_memory_load_exec (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (pf : PFunc) (op align offset : Nat) (address : UInt32) :
    exec cfg p (pushV s (.i32 address)) f pf (.load op align offset)=
      if address.toNat+offset+(loadSpec op).1>memBytes s then .abort s trapMem
      else .cont (setFrame (pushV s (preparedMemoryLoadedValue op
        (preparedScalarReadValue (fun i=>readByte s (address.toNat+offset+i)) (loadSpec op).1)))
        {f with pc:=f.pc+1}) := by
  rw [←prepared_scalar_read_exact]
  simp only [exec,popN,popV,pushV,Array.back?_push,Option.getD_some,Array.pop_push]
  rcases h:loadSpec op with ⟨width,signed,is64⟩
  simp only [h,preparedMemoryLoadedValue]
  cases is64 <;> rfl

theorem prepared_memory_store_i32_exec (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (pf : PFunc) (op align offset : Nat) (address value : UInt32) :
    exec cfg p (pushV (pushV s (.i32 address)) (.i32 value)) f pf (.store op align offset)=
      if address.toNat+offset+storeWidth op>memBytes s then .abort s trapMem
      else .cont (setFrame (executeByteRequests s (preparedScalarWriteRequests
        (address.toNat+offset) (storeWidth op) (value.toNat%256^(storeWidth op)))) {f with pc:=f.pc+1}) := by
  rw [←prepared_scalar_write_exact]
  simp only [exec,popN,popV,pushV,Array.back?_push,Option.getD_some,Array.pop_push]

theorem prepared_memory_store_i64_exec (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (pf : PFunc) (op align offset : Nat) (address : UInt32) (value : UInt64) :
    exec cfg p (pushV (pushV s (.i32 address)) (.i64 value)) f pf (.store op align offset)=
      if address.toNat+offset+storeWidth op>memBytes s then .abort s trapMem
      else .cont (setFrame (executeByteRequests s (preparedScalarWriteRequests
        (address.toNat+offset) (storeWidth op) (value.toNat%256^(storeWidth op)))) {f with pc:=f.pc+1}) := by
  rw [←prepared_scalar_write_exact]
  simp only [exec,popN,popV,pushV,Array.back?_push,Option.getD_some,Array.pop_push]

/-- Hash consistency applies to the exact state produced after popping both
store operands. This check executes natural bounds and ordered byte binding;
source AIR, gas charge and the enclosing initial commitment remain separate. -/
theorem prepared_memory_store_i64_commitment (hash : Bytes→ByteArray)
    (digestBound : ∀bs,bytesWireWf (hash bs)) (block count depth : Nat)
    (cfg : NearCfg) (p : Prepared) (s : St) (full : fullPages s.pages)
    (f : Frame) (pf : PFunc) (op align offset : Nat) (address : UInt32) (value : UInt64)
    (ws : List PageBatchWitness) (output : BlockDescriptor)
    (accepted : preparedScalarStoreCheck hash (describeSubpageMemory hash s block count depth)
      (address.toNat+offset) (storeWidth op) (value.toNat%256^(storeWidth op)) ws=some output) :
    (∃next,exec cfg p (pushV (pushV s (.i32 address)) (.i64 value)) f pf (.store op align offset)=.cont next ∧
      output=describeSubpageMemory hash next block count depth) ∨ blockBatchCollision hash block count depth s ws := by
  obtain ⟨_,bounds,result⟩:=prepared_scalar_store_checked hash digestBound block count depth s full _ _ _ ws output accepted
  rcases result with correct|collision
  · apply Or.inl
    refine ⟨setFrame (writeLE s (address.toNat+offset) (storeWidth op) (value.toNat%256^(storeWidth op))) {f with pc:=f.pc+1},?_,?_⟩
    · rw [prepared_memory_store_i64_exec,ite_eq_right (by omega),←prepared_scalar_write_exact]
    · unfold setFrame
      split <;> exact correct
  · exact Or.inr collision
end NearCompression
