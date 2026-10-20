import NearCompression.BlockBatch

/-! Executable single-opening batch verification against a memory descriptor.
The initial descriptor still needs authentication by the enclosing statement. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def checkBlockBatch (hash : Bytes → ByteArray) (d : BlockDescriptor) (index : Nat)
    (claimed : ByteArray) (path : List (Bool × ByteArray)) (writes : List (Nat × UInt8)) :
    Option BlockDescriptor :=
  if decide (0 < d.block) && decide (d.block * d.perPage = pageSize) &&
      decide (d.pages * d.perPage ≤ 2 ^ d.depth) && decide (index < d.pages * d.perPage) &&
      decide (claimed.size = d.block) && checkWriteWitnessWf ⟨0, 0, claimed, path⟩ &&
      writes.all (fun w => decide (w.1 < d.block)) &&
      decide (path.map Prod.fst = pageIndexPath d.depth index) &&
      decide (d.root = pageOpeningRoot (blockTreeHash hash d.block) claimed path) then
    some { d with root := pageOpeningRoot (blockTreeHash hash d.block) (applyPageWrites claimed writes) path }
  else none

theorem execute_byte_requests_page_count (s : St) (requests : List (Nat × UInt8)) :
    (executeByteRequests s requests).pages.size = s.pages.size := by
  induction requests generalizing s with
  | nil => rfl
  | cons r rs ih =>
    change (executeByteRequests (writeByte s r.1 r.2) rs).pages.size = _
    rw [ih]
    exact Array.size_modify

theorem checked_block_batch_correct_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (s : St) (full : fullPages s.pages)
    (block count depth index : Nat) (claimed : ByteArray) (path : List (Bool × ByteArray))
    (writes : List (Nat × UInt8)) (output : BlockDescriptor)
    (accepted : checkBlockBatch hash (describeSubpageMemory hash s block count depth)
      index claimed path writes = some output) :
    output = describeSubpageMemory hash
      (executeByteRequests s (blockBatchRequests block index writes)) block count depth ∨
    PageCollisionIn hash
      ((pageTreeMessages (blockTreeHash hash block) (buildSubpageTree s block count depth)).map (blockHashMessage block))
      ((pageOpeningMessages (blockTreeHash hash block) claimed path).map (blockHashMessage block)) := by
  unfold checkBlockBatch at accepted
  split at accepted
  · rename_i passed
    dsimp only [describeSubpageMemory] at passed
    have checks : 0 < block ∧ block * count = pageSize ∧ s.pages.size * count ≤ 2 ^ depth ∧
        index < s.pages.size * count ∧ claimed.size = block ∧
        memoryWriteWitnessWf ⟨0, 0, claimed, path⟩ ∧ (∀ w ∈ writes, w.1 < block) ∧
        path.map Prod.fst = pageIndexPath depth index ∧
        pageTreeRoot (blockTreeHash hash block) (buildSubpageTree s block count depth) =
          pageOpeningRoot (blockTreeHash hash block) claimed path := by
      simp only [Bool.and_eq_true, and_assoc] at passed
      obtain ⟨hp, hl, hc, ha, hs, hw, hf, hd, hr⟩ := passed
      refine ⟨of_decide_eq_true hp, of_decide_eq_true hl, of_decide_eq_true hc,
        of_decide_eq_true ha, of_decide_eq_true hs,
        (check_write_witness_wf_correct _).mp hw, ?_, of_decide_eq_true hd, of_decide_eq_true hr⟩
      intro w member
      exact of_decide_eq_true (List.all_eq_true.mp hf w member)
    obtain ⟨positive, layout, capacity, allocated, _size, wf, fits, directions, root⟩ := checks
    rcases subpage_batch_root_or_collision hash digestBound s full block count depth index
      positive layout capacity allocated writes fits claimed wf.1 path wf.2 directions root with correct | collision
    · apply Or.inl
      rw [← Option.some.inj accepted]
      change BlockDescriptor.mk block count s.pages.size depth
        (pageOpeningRoot (blockTreeHash hash block) (applyPageWrites claimed writes) path) =
        BlockDescriptor.mk block count
          (executeByteRequests s (blockBatchRequests block index writes)).pages.size depth
          (pageTreeRoot (blockTreeHash hash block)
            (buildSubpageTree (executeByteRequests s (blockBatchRequests block index writes)) block count depth))
      rw [execute_byte_requests_page_count, correct]
    · exact Or.inr collision
  · contradiction

end NearCompression
