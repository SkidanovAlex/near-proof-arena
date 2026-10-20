import NearCompression.BlockDescriptor

/-! An accepted block read binds both metadata and the memory opening.
The reference descriptor must still be authenticated by the enclosing state
statement. This is a deterministic collision reduction, not quantum extraction. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

theorem authenticated_block_read_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (s : St) (full : fullPages s.pages)
    (block count depth address : Nat)
    (referenceWf : blockDescriptorWf (describeSubpageMemory hash s block count depth))
    (descriptor : BlockDescriptor) (descriptorWf : blockDescriptorWf descriptor)
    (bound : hash (encodeBlockDescriptor (describeSubpageMemory hash s block count depth)) =
      hash (encodeBlockDescriptor descriptor))
    (claimed : ByteArray) (claimWf : bytesWireWf claimed)
    (path : List (Bool × ByteArray)) (pathWf : pageOpeningWf path)
    (passed : checkBlockOpening hash descriptor address claimed path = true) :
    readByte s address = claimed[address % descriptor.block]! ∨
    PageCollisionIn hash
      (encodeBlockDescriptor (describeSubpageMemory hash s block count depth) ::
        (pageTreeMessages (blockTreeHash hash block) (buildSubpageTree s block count depth)).map
          (blockHashMessage block))
      (encodeBlockDescriptor descriptor ::
        (pageOpeningMessages (blockTreeHash hash descriptor.block) claimed path).map
          (blockHashMessage descriptor.block)) := by
  rcases block_descriptor_binding_or_collision hash _ descriptor referenceWf descriptorWf bound with same | collision
  · subst descriptor
    have accepted := (check_block_opening_correct hash _ address claimed path).mp passed
    obtain ⟨positive, layout, capacity, allocated, _size, directions, root⟩ := accepted
    rcases subpage_committed_read_or_collision hash digestBound s full block count depth address
      positive layout capacity allocated claimed claimWf path pathWf directions root with correct | collision
    · exact Or.inl correct
    · apply Or.inr
      obtain ⟨m, hm, n, hn, different, equal⟩ := collision
      exact ⟨m, List.mem_cons_of_mem _ hm, n, List.mem_cons_of_mem _ hn, different, equal⟩
  · exact Or.inr ⟨_, List.mem_cons_self, _, List.mem_cons_self, collision.1, collision.2⟩

end NearCompression
