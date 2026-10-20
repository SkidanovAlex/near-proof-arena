import NearCompression.UntrustedPageUpdate

/-! Sequential checked byte writes and actual-state invariants. Bulk instruction
semantics and whole-state boundary linkage remain separate obligations. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def memoryPagesWf (s : St) : Prop := ∀ p ∈ s.pages.toList, bytesWireWf p

theorem bytes_wire_wf_set (p : ByteArray) (wf : bytesWireWf p) (index : Nat) (value : UInt8) :
    bytesWireWf (p.set! index value) := by
  simpa only [bytesWireWf, Array.length_toList, ByteArray.size_data, ByteArray.size_set!] using wf

theorem write_byte_pages_wf (s : St) (wf : memoryPagesWf s) (address : Nat) (value : UInt8) :
    memoryPagesWf (writeByte s address value) := by
  intro p hp
  have hm : p ∈ (s.pages.modify (address / pageSize) (fun p => p.set! (address % pageSize) value)) := by
    exact Array.mem_toList_iff.mp hp
  obtain ⟨i, hi, he⟩ := Array.getElem_of_mem hm
  rw [Array.getElem_modify] at he
  have originalWf : bytesWireWf (s.pages[i]'(by simpa using hi)) := wf _ (by simp)
  split at he
  · rw [← he]; exact bytes_wire_wf_set _ originalWf _ _
  · rw [← he]; exact originalWf

theorem describe_memory_wf (hash : Bytes → ByteArray) (digestBound : ∀ bs, bytesWireWf (hash bs))
    (s : St) (depth : Nat) (countBound : nat128WireWf s.pages.size) (depthBound : nat128WireWf depth) :
    memoryDescriptorWf (describeMemory hash s depth) := by
  refine ⟨countBound, depthBound, ?_⟩
  change bytesWireWf (pageTreeRoot hash (buildPageTree s.pages depth 0))
  cases he : buildPageTree s.pages depth 0 <;> exact digestBound _

structure MemoryWriteWitness where
  address : Nat
  value : UInt8
  page : ByteArray
  path : List (Bool × ByteArray)

def memoryWriteWitnessWf (w : MemoryWriteWitness) : Prop :=
  bytesWireWf w.page ∧ pageOpeningWf w.path

def executeMemoryWrites : St → List MemoryWriteWitness → St
  | s, [] => s
  | s, w :: ws => executeMemoryWrites (writeByte s w.address w.value) ws

def checkMemoryWrites (hash : Bytes → ByteArray) : MemoryDescriptor → List MemoryWriteWitness → Option MemoryDescriptor
  | d, [] => some d
  | d, w :: ws => (checkedMemoryByteWrite hash d w.address w.page w.path w.value).bind
      (fun next => checkMemoryWrites hash next ws)

def memoryWriteCollision (hash : Bytes → ByteArray) (depth : Nat) : St → List MemoryWriteWitness → Prop
  | _, [] => False
  | s, w :: ws =>
    PageCollisionIn hash
      (encodeMemoryDescriptor (describeMemory hash s depth) :: pageTreeMessages hash (buildPageTree s.pages depth 0))
      (encodeMemoryDescriptor (describeMemory hash s depth) :: pageOpeningMessages hash w.page w.path) ∨
    memoryWriteCollision hash depth (writeByte s w.address w.value) ws

theorem checked_memory_write_chain (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (depth : Nat) (depthBound : nat128WireWf depth)
    (s : St) (pagesWf : memoryPagesWf s) (countBound : nat128WireWf s.pages.size)
    (ws : List MemoryWriteWitness) (witnessWf : ∀ w ∈ ws, memoryWriteWitnessWf w)
    (output : MemoryDescriptor)
    (accepted : checkMemoryWrites hash (describeMemory hash s depth) ws = some output) :
    output = describeMemory hash (executeMemoryWrites s ws) depth ∨ memoryWriteCollision hash depth s ws := by
  induction ws generalizing s output with
  | nil =>
    exact Or.inl (Option.some.inj accepted).symm
  | cons w ws ih =>
    have hw := witnessWf w (by simp)
    have hd := describe_memory_wf hash digestBound s depth countBound depthBound
    by_cases hc : checkMemoryPage hash (describeMemory hash s depth) (w.address / pageSize) w.page w.path = true
    · rcases committed_memory_write_or_collision hash digestBound s depth w.address _ hd hd rfl
        pagesWf w.page hw.1 w.path hw.2 hc w.value with he | hcol
      · simp only [checkMemoryWrites, he, Option.bind_some] at accepted
        have hcount : nat128WireWf (writeByte s w.address w.value).pages.size := by
          simpa only [writeByte, Array.size_modify] using countBound
        rcases ih (writeByte s w.address w.value) (write_byte_pages_wf s pagesWf _ _) hcount
          (fun v hv => witnessWf v (by simp [hv])) output accepted with hout | hcollision
        · exact Or.inl hout
        · exact Or.inr (Or.inr hcollision)
      · exact Or.inr (Or.inl hcol)
    · simp [checkMemoryWrites, checkedMemoryByteWrite, hc] at accepted

end NearCompression
