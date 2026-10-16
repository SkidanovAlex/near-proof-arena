import NearCompression.AuthenticatedBlockWrite

/-! An accepted block update binds metadata and the resulting Wasm memory root.
The reference descriptor must still be authenticated by the enclosing state
statement. This is a deterministic collision reduction, not quantum extraction. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def checkedBlockByteWrite (hash : Bytes → ByteArray) (descriptor : BlockDescriptor)
    (address : Nat) (claimed : ByteArray) (path : List (Bool × ByteArray)) (value : UInt8) :
    Option BlockDescriptor :=
  if checkBlockOpening hash descriptor address claimed path then
    some { descriptor with root := pageOpeningRoot (blockTreeHash hash descriptor.block) (claimed.set! (address % descriptor.block) value) path }
  else none

theorem checked_block_write_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (s : St) (full : fullPages s.pages)
    (block count depth address : Nat)
    (referenceWf : blockDescriptorWf (describeSubpageMemory hash s block count depth))
    (descriptor : BlockDescriptor) (descriptorWf : blockDescriptorWf descriptor)
    (bound : hash (encodeBlockDescriptor (describeSubpageMemory hash s block count depth)) =
      hash (encodeBlockDescriptor descriptor))
    (claimed : ByteArray) (claimWf : bytesWireWf claimed)
    (path : List (Bool × ByteArray)) (pathWf : pageOpeningWf path)
    (passed : checkBlockOpening hash descriptor address claimed path = true) (value : UInt8) :
    checkedBlockByteWrite hash descriptor address claimed path value =
      some (describeSubpageMemory hash (writeByte s address value) block count depth) ∨
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
    rcases subpage_committed_write_or_collision hash digestBound s full block count depth address
      positive layout capacity allocated claimed claimWf path pathWf directions root value with correct | collision
    · apply Or.inl
      simp only [checkedBlockByteWrite, passed, if_true]
      have hs : (writeByte s address value).pages.size = s.pages.size := Array.size_modify
      change some (BlockDescriptor.mk block count s.pages.size depth
        (pageOpeningRoot (blockTreeHash hash block) (claimed.set! (address % block) value) path)) =
        some (BlockDescriptor.mk block count (writeByte s address value).pages.size depth
          (pageTreeRoot (blockTreeHash hash block)
            (buildSubpageTree (writeByte s address value) block count depth)))
      rw [hs, correct]
    · apply Or.inr
      obtain ⟨m, hm, n, hn, different, equal⟩ := collision
      exact ⟨m, List.mem_cons_of_mem _ hm, n, List.mem_cons_of_mem _ hn, different, equal⟩
  · exact Or.inr ⟨_, List.mem_cons_self, _, List.mem_cons_self, collision.1, collision.2⟩

end NearCompression
