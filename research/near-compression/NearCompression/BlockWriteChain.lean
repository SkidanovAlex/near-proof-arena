import NearCompression.CheckedBlockWrite

/-! Descriptor-threaded block openings refine ordered actual Wasm byte writes.
Witness transport, full-state binding and AIR constraints remain separate. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

theorem describe_subpage_memory_wf (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (s : St) (block count depth : Nat)
    (blockBound : nat128WireWf block) (countBound : nat128WireWf count)
    (pagesBound : nat128WireWf s.pages.size) (depthBound : nat128WireWf depth) :
    blockDescriptorWf (describeSubpageMemory hash s block count depth) := by
  refine ⟨blockBound, countBound, pagesBound, depthBound, ?_⟩
  change bytesWireWf (pageTreeRoot (blockTreeHash hash block) (buildSubpageTree s block count depth))
  cases he : buildSubpageTree s block count depth <;> exact digestBound _

def checkBlockWrites (hash : Bytes → ByteArray) : BlockDescriptor → List MemoryWriteWitness → Option BlockDescriptor
  | d, [] => some d
  | d, w :: ws => (checkedBlockByteWrite hash d w.address w.page w.path w.value).bind
      (fun next => checkBlockWrites hash next ws)

def blockWriteCollision (hash : Bytes → ByteArray) (block count depth : Nat) : St → List MemoryWriteWitness → Prop
  | _, [] => False
  | s, w :: ws =>
    PageCollisionIn hash
      (encodeBlockDescriptor (describeSubpageMemory hash s block count depth) ::
        (pageTreeMessages (blockTreeHash hash block) (buildSubpageTree s block count depth)).map (blockHashMessage block))
      (encodeBlockDescriptor (describeSubpageMemory hash s block count depth) ::
        (pageOpeningMessages (blockTreeHash hash block) w.page w.path).map (blockHashMessage block)) ∨
    blockWriteCollision hash block count depth (writeByte s w.address w.value) ws

theorem checked_block_write_chain (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (block count depth : Nat)
    (blockBound : nat128WireWf block) (countBound : nat128WireWf count) (depthBound : nat128WireWf depth)
    (s : St) (full : fullPages s.pages) (pagesBound : nat128WireWf s.pages.size)
    (ws : List MemoryWriteWitness) (witnessWf : ∀ w ∈ ws, memoryWriteWitnessWf w)
    (output : BlockDescriptor)
    (accepted : checkBlockWrites hash (describeSubpageMemory hash s block count depth) ws = some output) :
    output = describeSubpageMemory hash (executeMemoryWrites s ws) block count depth ∨
      blockWriteCollision hash block count depth s ws := by
  induction ws generalizing s output with
  | nil => exact Or.inl (Option.some.inj accepted).symm
  | cons w ws ih =>
    have hw := witnessWf w (by simp)
    have hd := describe_subpage_memory_wf hash digestBound s block count depth blockBound countBound pagesBound depthBound
    by_cases hc : checkBlockOpening hash (describeSubpageMemory hash s block count depth) w.address w.page w.path = true
    · rcases checked_block_write_or_collision hash digestBound s full block count depth w.address hd _ hd rfl
        w.page hw.1 w.path hw.2 hc w.value with he | hcol
      · simp only [checkBlockWrites, he, Option.bind_some] at accepted
        have hpages : nat128WireWf (writeByte s w.address w.value).pages.size := by
          simpa only [writeByte, Array.size_modify] using pagesBound
        rcases ih (writeByte s w.address w.value) (write_byte_full_pages s full _ _) hpages
          (fun v hv => witnessWf v (by simp [hv])) output accepted with hout | hcollision
        · exact Or.inl hout
        · exact Or.inr (Or.inr hcollision)
      · exact Or.inr (Or.inl hcol)
    · simp [checkBlockWrites, checkedBlockByteWrite, hc] at accepted

end NearCompression
