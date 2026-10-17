import NearCompression.IndexedPageTree

/-! Bind allocation count and chosen tree depth as well as the page-tree root.
Digest security and connection to the whole-state boundary remain separate. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

structure MemoryDescriptor where
  count : Nat
  depth : Nat
  root : ByteArray
  deriving DecidableEq

def memoryDescriptorDomain : Bytes := [110, 101, 97, 114, 112, 114, 111, 111, 102, 45, 109, 101, 109, 45, 118, 49]

def memoryDescriptorWf (d : MemoryDescriptor) : Prop :=
  nat128WireWf d.count ∧ nat128WireWf d.depth ∧ bytesWireWf d.root

def encodeMemoryDescriptor (d : MemoryDescriptor) : Bytes :=
  memoryDescriptorDomain ++ u128 d.count ++ u128 d.depth ++ encodeBytesWire d.root

/-- Payload parser; the fixed domain prefix is removed only in the injectivity
proof. There is no public parser that silently accepts an unchecked domain. -/
def parseMemoryDescriptorPayload : NearSpecV3.P MemoryDescriptor := fun bs => do
  let (count, bs) ← pU128 "counter" bs
  let (depth, bs) ← pU128 "counter" bs
  let (root, bs) ← parseBytesWire bs
  pure ({ count, depth, root }, bs)

theorem memory_descriptor_payload_roundtrip (d : MemoryDescriptor) (wf : memoryDescriptorWf d)
    (rest : Bytes) :
    parseMemoryDescriptorPayload (u128 d.count ++ u128 d.depth ++ encodeBytesWire d.root ++ rest) =
      .ok (d, rest) := by
  simp only [parseMemoryDescriptorPayload, List.append_assoc]
  rw [nat128_wire_roundtrip d.count wf.1]
  simp only [bind, Except.bind]
  rw [nat128_wire_roundtrip d.depth wf.2.1]
  simp only [bind, Except.bind]
  rw [bytes_wire_roundtrip d.root wf.2.2]
  rfl

theorem memory_descriptor_encoding_injective (a b : MemoryDescriptor)
    (ha : memoryDescriptorWf a) (hb : memoryDescriptorWf b)
    (same : encodeMemoryDescriptor a = encodeMemoryDescriptor b) : a = b := by
  have h : u128 a.count ++ u128 a.depth ++ encodeBytesWire a.root =
      u128 b.count ++ u128 b.depth ++ encodeBytesWire b.root := by
    simpa only [encodeMemoryDescriptor, List.append_assoc, List.append_cancel_left_eq] using same
  have he := congrArg (fun bs => parseMemoryDescriptorPayload (bs ++ [])) h
  rw [memory_descriptor_payload_roundtrip a ha [], memory_descriptor_payload_roundtrip b hb []] at he
  exact congrArg Prod.fst (Except.ok.inj he)

def describeMemory (hash : Bytes → ByteArray) (s : St) (depth : Nat) : MemoryDescriptor :=
  ⟨s.pages.size, depth, pageTreeRoot hash (buildPageTree s.pages depth 0)⟩

theorem memory_descriptor_binding_or_collision (hash : Bytes → ByteArray)
    (a b : MemoryDescriptor) (ha : memoryDescriptorWf a) (hb : memoryDescriptorWf b)
    (same : hash (encodeMemoryDescriptor a) = hash (encodeMemoryDescriptor b)) :
    a = b ∨ (encodeMemoryDescriptor a ≠ encodeMemoryDescriptor b ∧
      hash (encodeMemoryDescriptor a) = hash (encodeMemoryDescriptor b)) := by
  classical
  by_cases he : encodeMemoryDescriptor a = encodeMemoryDescriptor b
  · exact Or.inl (memory_descriptor_encoding_injective a b ha hb he)
  · exact Or.inr ⟨he, same⟩

/-- A real ambiguity of a root alone: empty allocation and one empty page.
The descriptor carries the allocation count to prevent this reinterpretation. -/
theorem padded_root_allocation_ambiguity (hash : Bytes → ByteArray) :
    pageTreeRoot hash (buildPageTree #[] 0 0) =
      pageTreeRoot hash (buildPageTree #[ByteArray.empty] 0 0) := rfl

theorem memory_descriptor_count_distinct (a b : MemoryDescriptor)
    (ha : memoryDescriptorWf a) (hb : memoryDescriptorWf b) (different : a.count ≠ b.count) :
    encodeMemoryDescriptor a ≠ encodeMemoryDescriptor b := by
  intro he
  exact different (congrArg MemoryDescriptor.count (memory_descriptor_encoding_injective a b ha hb he))

def acceptsMemoryPage (hash : Bytes → ByteArray) (d : MemoryDescriptor)
    (index : Nat) (page : ByteArray) (path : List (Bool × ByteArray)) : Prop :=
  index < d.count ∧ d.count ≤ 2 ^ d.depth ∧
    path.map Prod.fst = pageIndexPath d.depth index ∧
    d.root = pageOpeningRoot hash page path

/-- The count check prevents a padding leaf from authorizing a byte read. Both
metadata and page collisions are located in the actual compared messages. -/
theorem committed_memory_read_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (s : St) (depth address : Nat)
    (claimed : MemoryDescriptor)
    (honestWf : memoryDescriptorWf (describeMemory hash s depth))
    (claimedWf : memoryDescriptorWf claimed)
    (same : hash (encodeMemoryDescriptor (describeMemory hash s depth)) =
      hash (encodeMemoryDescriptor claimed))
    (pagesWf : ∀ p ∈ s.pages.toList, bytesWireWf p)
    (page : ByteArray) (pageWf : bytesWireWf page)
    (path : List (Bool × ByteArray)) (pathWf : pageOpeningWf path)
    (accepted : acceptsMemoryPage hash claimed (address / pageSize) page path) :
    readByte s address = page.get! (address % pageSize) ∨
      PageCollisionIn hash
        (encodeMemoryDescriptor (describeMemory hash s depth) ::
          pageTreeMessages hash (buildPageTree s.pages depth 0))
        (encodeMemoryDescriptor claimed :: pageOpeningMessages hash page path) := by
  rcases memory_descriptor_binding_or_collision hash _ claimed honestWf claimedWf same with he | hc
  · subst claimed
    obtain ⟨hi, capacity, directions, root⟩ := accepted
    change address / pageSize < s.pages.size at hi
    let original := s.pages[address / pageSize]
    have present : s.pages[address / pageSize]? = some original := by simp [original, hi]
    rcases indexed_page_opening_or_collision hash digestBound s depth (address / pageSize)
      capacity original present pagesWf page pageWf path pathWf directions root with hp | hc
    · exact Or.inl (by simp only [readByte, present, hp])
    · obtain ⟨m, hm, n, hn, hne, hhash⟩ := hc
      exact Or.inr ⟨m, List.mem_cons_of_mem _ hm, n, List.mem_cons_of_mem _ hn, hne, hhash⟩
  · exact Or.inr ⟨_, List.mem_cons_self, _, List.mem_cons_self, hc⟩

def checkMemoryPage (hash : Bytes → ByteArray) (d : MemoryDescriptor)
    (index : Nat) (page : ByteArray) (path : List (Bool × ByteArray)) : Bool :=
  decide (index < d.count) && decide (d.count ≤ 2 ^ d.depth) &&
    decide (path.map Prod.fst = pageIndexPath d.depth index) &&
    decide (d.root = pageOpeningRoot hash page path)

theorem check_memory_page_correct (hash : Bytes → ByteArray) (d : MemoryDescriptor)
    (index : Nat) (page : ByteArray) (path : List (Bool × ByteArray)) :
    checkMemoryPage hash d index page path = true ↔ acceptsMemoryPage hash d index page path := by
  simp [checkMemoryPage, acceptsMemoryPage, and_assoc]

end NearCompression
