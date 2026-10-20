import NearCompression.PageTreeUpdate

/-! Untrusted supplied paths: accepted old roots bind both the old page and
updated root, or expose a collision in the finite compared hash messages. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

theorem page_tree_update_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs))
    (tree : PageTree) (treeWf : pageTreeWf tree) (page : ByteArray) (pageWf : bytesWireWf page)
    (path : List (Bool × ByteArray)) (pathWf : pageOpeningWf path)
    (replacement original : ByteArray) (lookup : pageTreeAt tree (path.map Prod.fst) = some original)
    (accepted : pageTreeRoot hash tree = pageOpeningRoot hash page path) :
    (original = page ∧
      pageTreeRoot hash (replacePageTree tree (path.map Prod.fst) replacement) =
        pageOpeningRoot hash replacement path) ∨ PageCollisionIn hash (pageTreeMessages hash tree) (pageOpeningMessages hash page path) := by
  classical
  have rootBound : ∀ t, bytesWireWf (pageTreeRoot hash t) := by
    intro t; cases t <;> exact digestBound _
  have openingBound : ∀ p, bytesWireWf (pageOpeningRoot hash page p) := by
    intro p; cases p <;> exact digestBound _
  induction tree generalizing path with
  | leaf p =>
    cases path with
    | nil =>
      have ho : p = original := Option.some.inj lookup
      subst original
      by_cases same : encodeMemoryPage p = encodeMemoryPage page
      · exact Or.inl ⟨memory_page_encoding_injective p page treeWf pageWf same, rfl⟩
      · exact Or.inr ⟨_, by simp [pageTreeMessages], _, by simp [pageOpeningMessages], same, accepted⟩
    | cons x xs => simp [pageTreeAt] at lookup
  | node l r il ir =>
    cases path with
    | nil => simp [pageTreeAt] at lookup
    | cons x rest =>
      obtain ⟨right, sibling⟩ := x
      have hs : bytesWireWf sibling := pathWf (right, sibling) (by simp)
      have ht : pageOpeningWf rest := fun x hx => pathWf x (by simp [hx])
      cases right with
      | false =>
        have ha : pageTreeAt l (rest.map Prod.fst) = some original := lookup
        have hh : hash (encodePageNode (pageTreeRoot hash l) (pageTreeRoot hash r)) =
            hash (encodePageNode (pageOpeningRoot hash page rest) sibling) := accepted
        by_cases same : encodePageNode (pageTreeRoot hash l) (pageTreeRoot hash r) =
            encodePageNode (pageOpeningRoot hash page rest) sibling
        · have hc := page_node_encoding_injective _ _ _ _ (rootBound l) (rootBound r)
            (openingBound rest) hs same
          rcases il treeWf.1 rest ht ha hc.1 with he | hcol
          · refine Or.inl ⟨he.1, ?_⟩
            change hash (encodePageNode
              (pageTreeRoot hash (replacePageTree l (rest.map Prod.fst) replacement)) (pageTreeRoot hash r)) =
              hash (encodePageNode (pageOpeningRoot hash replacement rest) sibling)
            rw [he.2, hc.2]
          · obtain ⟨m, hm, n, hn, hne, heq⟩ := hcol
            exact Or.inr ⟨m, List.mem_cons_of_mem _ (List.mem_append_left _ hm),
              n, List.mem_cons_of_mem _ hn, hne, heq⟩
        · exact Or.inr ⟨_, List.mem_cons_self, _, List.mem_cons_self, same, hh⟩
      | true =>
        have ha : pageTreeAt r (rest.map Prod.fst) = some original := lookup
        have hh : hash (encodePageNode (pageTreeRoot hash l) (pageTreeRoot hash r)) =
            hash (encodePageNode sibling (pageOpeningRoot hash page rest)) := accepted
        by_cases same : encodePageNode (pageTreeRoot hash l) (pageTreeRoot hash r) =
            encodePageNode sibling (pageOpeningRoot hash page rest)
        · have hc := page_node_encoding_injective _ _ _ _ (rootBound l) (rootBound r)
            hs (openingBound rest) same
          rcases ir treeWf.2 rest ht ha hc.2 with he | hcol
          · refine Or.inl ⟨he.1, ?_⟩
            change hash (encodePageNode (pageTreeRoot hash l)
              (pageTreeRoot hash (replacePageTree r (rest.map Prod.fst) replacement))) =
              hash (encodePageNode sibling (pageOpeningRoot hash replacement rest))
            rw [he.2, hc.1]
          · obtain ⟨m, hm, n, hn, hne, heq⟩ := hcol
            exact Or.inr ⟨m, List.mem_cons_of_mem _ (List.mem_append_right _ hm),
              n, List.mem_cons_of_mem _ hn, hne, heq⟩
        · exact Or.inr ⟨_, List.mem_cons_self, _, List.mem_cons_self, same, hh⟩

theorem untrusted_write_byte_root_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (s : St) (depth address : Nat)
    (capacity : s.pages.size ≤ 2 ^ depth) (allocated : address / pageSize < s.pages.size)
    (pagesWf : ∀ p ∈ s.pages.toList, bytesWireWf p)
    (page : ByteArray) (pageWf : bytesWireWf page) (path : List (Bool × ByteArray))
    (pathWf : pageOpeningWf path)
    (directions : path.map Prod.fst = pageIndexPath depth (address / pageSize))
    (accepted : pageTreeRoot hash (buildPageTree s.pages depth 0) = pageOpeningRoot hash page path)
    (value : UInt8) :
    pageTreeRoot hash (buildPageTree (writeByte s address value).pages depth 0) =
      pageOpeningRoot hash (page.set! (address % pageSize) value) path ∨
    PageCollisionIn hash (pageTreeMessages hash (buildPageTree s.pages depth 0))
      (pageOpeningMessages hash page path) := by
  let original := s.pages[address / pageSize]
  have present : s.pages[address / pageSize]? = some original := by simp [original, allocated]
  have lookup : pageTreeAt (buildPageTree s.pages depth 0) (path.map Prod.fst) = some original := by
    rw [directions, built_page_tree_lookup s.pages depth 0 (address / pageSize) (by omega)]
    simp [memoryPageAt, present]
  rcases page_tree_update_or_collision hash digestBound _ (built_page_tree_wf s.pages pagesWf depth 0)
    page pageWf path pathWf (page.set! (address % pageSize) value) original lookup accepted with he | hc
  · apply Or.inl
    rw [write_byte_page_tree s depth address capacity allocated original present value, he.1, ← directions]
    exact he.2
  · exact Or.inr hc

def checkedMemoryByteWrite (hash : Bytes → ByteArray) (d : MemoryDescriptor)
    (address : Nat) (page : ByteArray) (path : List (Bool × ByteArray)) (value : UInt8) :
    Option MemoryDescriptor :=
  if checkMemoryPage hash d (address / pageSize) page path then
    some { d with root := pageOpeningRoot hash (page.set! (address % pageSize) value) path }
  else none

/-- Successful checked writes refine the actual byte-write memory descriptor,
or locate a collision in the metadata/tree/opening messages. -/
theorem committed_memory_write_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (s : St) (depth address : Nat)
    (claimed : MemoryDescriptor)
    (honestWf : memoryDescriptorWf (describeMemory hash s depth))
    (claimedWf : memoryDescriptorWf claimed)
    (same : hash (encodeMemoryDescriptor (describeMemory hash s depth)) =
      hash (encodeMemoryDescriptor claimed))
    (pagesWf : ∀ p ∈ s.pages.toList, bytesWireWf p)
    (page : ByteArray) (pageWf : bytesWireWf page)
    (path : List (Bool × ByteArray)) (pathWf : pageOpeningWf path)
    (accepted : checkMemoryPage hash claimed (address / pageSize) page path = true)
    (value : UInt8) :
    checkedMemoryByteWrite hash claimed address page path value =
      some (describeMemory hash (writeByte s address value) depth) ∨
    PageCollisionIn hash
      (encodeMemoryDescriptor (describeMemory hash s depth) ::
        pageTreeMessages hash (buildPageTree s.pages depth 0))
      (encodeMemoryDescriptor claimed :: pageOpeningMessages hash page path) := by
  rcases memory_descriptor_binding_or_collision hash _ claimed honestWf claimedWf same with he | hc
  · subst claimed
    obtain ⟨hi, capacity, directions, root⟩ := (check_memory_page_correct _ _ _ _ _).mp accepted
    change address / pageSize < s.pages.size at hi
    rcases untrusted_write_byte_root_or_collision hash digestBound s depth address capacity hi
      pagesWf page pageWf path pathWf directions root value with he | hc
    · apply Or.inl
      simp only [checkedMemoryByteWrite, accepted, if_true]
      have hs : (writeByte s address value).pages.size = s.pages.size := Array.size_modify
      change some (MemoryDescriptor.mk s.pages.size depth
        (pageOpeningRoot hash (page.set! (address % pageSize) value) path)) =
        some (MemoryDescriptor.mk (writeByte s address value).pages.size depth
          (pageTreeRoot hash (buildPageTree (writeByte s address value).pages depth 0)))
      rw [hs, he]
    · obtain ⟨m, hm, n, hn, hne, hhash⟩ := hc
      exact Or.inr ⟨m, List.mem_cons_of_mem _ hm, n, List.mem_cons_of_mem _ hn, hne, hhash⟩
  · exact Or.inr ⟨_, List.mem_cons_self, _, List.mem_cons_self, hc⟩

end NearCompression
