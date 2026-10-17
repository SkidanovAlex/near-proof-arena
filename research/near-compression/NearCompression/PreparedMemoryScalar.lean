import NearCompression.BlockBatchChain
import NearCompression.PreparedTypedStep
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm
/-- Ordered byte requests of the actual scalar store. Effective addresses are
natural sums; this definition deliberately performs no u32 address reduction. -/
def preparedScalarWriteRequests (address width value : Nat) : List (Nat × UInt8) :=
  (List.range' 0 width).map (fun i=>(address+i,UInt8.ofNat ((value/256^i)%256)))

def preparedScalarReadValue (bytes : Nat→UInt8) (width : Nat) : Nat :=
  (List.range' 0 width).foldl (fun value i=>value+(bytes i).toNat*256^i) 0

private theorem plain_for_in_fold {α β : Type} (xs : List α) (f : β→α→β) (s : β) :
    (forIn (m:=Id) xs s (fun i st=>ForInStep.yield (f st i)))=xs.foldl f s := by
  induction xs generalizing s with
  | nil=>rfl
  | cons x xs ih=>simp only [List.forIn_cons,List.foldl_cons];exact ih (f s x)

theorem prepared_scalar_read_exact (s : St) (address width : Nat) :
    readLE s address width=preparedScalarReadValue (fun i=>readByte s (address+i)) width := by
  unfold NearSpecV3.Wasm.readLE preparedScalarReadValue
  simp only [Id.run,Std.Legacy.Range.forIn_eq_forIn_range']
  simpa [Std.Legacy.Range.size,bind,pure] using
    plain_for_in_fold (List.range' 0 width) (fun value i=>value+(readByte s (address+i)).toNat*256^i) 0

theorem prepared_scalar_write_exact (s : St) (address width value : Nat) :
    writeLE s address width value=executeByteRequests s (preparedScalarWriteRequests address width value) := by
  unfold writeLE executeByteRequests preparedScalarWriteRequests
  simp only [Id.run,Std.Legacy.Range.forIn_eq_forIn_range',List.foldl_map]
  simpa [Std.Legacy.Range.size,bind,pure] using
    plain_for_in_fold (List.range' 0 width) (fun st i=>writeByte st (address+i) (UInt8.ofNat ((value/256^i)%256))) s

/-- Scalar stores share the existing subpage batching checker, binding the
exact ordered byte stream. Hash evaluation is outside AIR at this layer. -/
def preparedScalarStoreCheck (hash : Bytes→ByteArray) (initial : BlockDescriptor)
    (address width value : Nat) (ws : List PageBatchWitness) : Option BlockDescriptor :=
  if (width=1 ∨ width=2 ∨ width=4 ∨ width=8) ∧ address+width≤initial.pages*pageSize ∧
      blockBatchSequenceRequests initial.block ws=preparedScalarWriteRequests address width value then
    checkBlockBatches hash initial ws
  else none

theorem prepared_scalar_store_checked (hash : Bytes→ByteArray)
    (digestBound : ∀bs,bytesWireWf (hash bs)) (block count depth : Nat)
    (s : St) (full : fullPages s.pages) (address width value : Nat)
    (ws : List PageBatchWitness) (output : BlockDescriptor)
    (accepted : preparedScalarStoreCheck hash (describeSubpageMemory hash s block count depth)
      address width value ws=some output) :
    (width=1 ∨ width=2 ∨ width=4 ∨ width=8) ∧ address+width≤memBytes s ∧
    (output=describeSubpageMemory hash (writeLE s address width value) block count depth ∨
      blockBatchCollision hash block count depth s ws) := by
  unfold preparedScalarStoreCheck at accepted
  split at accepted
  · rename_i checks
    refine ⟨checks.1,checks.2.1,?_⟩
    rcases checked_block_batch_chain hash digestBound block count depth s full ws output accepted with correct|collision
    · apply Or.inl
      have requests : blockBatchSequenceRequests block ws=preparedScalarWriteRequests address width value:=checks.2.2
      rw [execute_block_batches_requests,requests,←prepared_scalar_write_exact] at correct
      exact correct
    · exact Or.inr collision
  · contradiction
end NearCompression
