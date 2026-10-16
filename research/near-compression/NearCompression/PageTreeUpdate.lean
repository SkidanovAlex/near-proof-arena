import NearCompression.MemoryDescriptor

/-! Incremental tree replacement agrees with rebuilding the actual modified page
array. This is a semantic update theorem, not yet an untrusted-path verifier. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def replacePageTree : PageTree → List Bool → ByteArray → PageTree
  | .leaf _, [], p => .leaf p
  | .node l r, false :: rest, p => .node (replacePageTree l rest p) r
  | .node l r, true :: rest, p => .node l (replacePageTree r rest p)
  | tree, _, _ => tree

theorem build_page_tree_congr (a b : Array ByteArray) (depth oa ob : Nat)
    (same : ∀ i, i < 2 ^ depth → memoryPageAt a (oa + i) = memoryPageAt b (ob + i)) :
    buildPageTree a depth oa = buildPageTree b depth ob := by
  induction depth generalizing oa ob with
  | zero =>
    have h := same 0 (by decide)
    simpa [buildPageTree] using congrArg PageTree.leaf h
  | succ depth ih =>
    simp only [buildPageTree]
    congr 1
    · apply ih
      intro i hi
      apply same
      rw [Nat.pow_succ]
      omega
    · apply ih
      intro i hi
      have h := same (2 ^ depth + i) (by rw [Nat.pow_succ]; omega)
      simpa only [Nat.add_assoc] using h

theorem build_page_tree_modify_outside (pages : Array ByteArray) (depth offset target : Nat)
    (f : ByteArray → ByteArray) (outside : target < offset ∨ offset + 2 ^ depth ≤ target) :
    buildPageTree (pages.modify target f) depth offset = buildPageTree pages depth offset := by
  apply build_page_tree_congr
  intro i hi
  have hne : target ≠ offset + i := by omega
  simp only [memoryPageAt, Array.getElem?_modify, if_neg hne]

theorem memory_page_modify_target (pages : Array ByteArray) (target : Nat)
    (f : ByteArray → ByteArray) (inside : target < pages.size) :
    memoryPageAt (pages.modify target f) target = f (memoryPageAt pages target) := by
  simp [memoryPageAt, Array.getElem_modify, inside]

theorem build_page_tree_modify_inside (pages : Array ByteArray) (depth offset index : Nat)
    (f : ByteArray → ByteArray) (bound : index < 2 ^ depth)
    (allocated : offset + index < pages.size) :
    buildPageTree (pages.modify (offset + index) f) depth offset =
      replacePageTree (buildPageTree pages depth offset) (pageIndexPath depth index)
        (f (memoryPageAt pages (offset + index))) := by
  induction depth generalizing offset index with
  | zero =>
    have hi : index = 0 := by simpa using bound
    subst index
    simp only [Nat.add_zero, buildPageTree, pageIndexPath, replacePageTree]
    rw [memory_page_modify_target pages offset f (by simpa using allocated)]
  | succ depth ih =>
    simp only [buildPageTree, pageIndexPath]
    split
    · rename_i h
      simp only [replacePageTree]
      rw [ih offset index h allocated]
      rw [build_page_tree_modify_outside pages depth (offset + 2 ^ depth) (offset + index) f
        (Or.inl (by omega))]
    · rename_i h
      have hb : index - 2 ^ depth < 2 ^ depth := by
        rw [Nat.pow_succ] at bound
        omega
      have he : offset + index = (offset + 2 ^ depth) + (index - 2 ^ depth) := by omega
      simp only [replacePageTree]
      rw [build_page_tree_modify_outside pages depth offset (offset + index) f (Or.inr (by omega))]
      rw [he, ih _ _ hb (by omega)]

theorem write_byte_page_tree (s : St) (depth address : Nat)
    (capacity : s.pages.size ≤ 2 ^ depth) (allocated : address / pageSize < s.pages.size)
    (page : ByteArray) (present : s.pages[address / pageSize]? = some page) (value : UInt8) :
    buildPageTree (writeByte s address value).pages depth 0 =
      replacePageTree (buildPageTree s.pages depth 0) (pageIndexPath depth (address / pageSize))
        (page.set! (address % pageSize) value) := by
  have h := build_page_tree_modify_inside s.pages depth 0 (address / pageSize)
    (fun p => p.set! (address % pageSize) value) (by omega) (by omega)
  simpa [writeByte, memoryPageAt, present] using h

/-- Reuse the existing siblings; only the leaf-to-root hashes change. -/
theorem built_opening_replacement_root (hash : Bytes → ByteArray) (pages : Array ByteArray)
    (depth offset index : Nat) (replacement : ByteArray) :
    pageOpeningRoot hash replacement (buildPageOpening hash pages depth offset index) =
      pageTreeRoot hash (replacePageTree (buildPageTree pages depth offset)
        (pageIndexPath depth index) replacement) := by
  induction depth generalizing offset index with
  | zero => rfl
  | succ depth ih =>
    simp only [buildPageOpening, buildPageTree, pageIndexPath]
    split <;> simp [pageOpeningRoot, replacePageTree, pageTreeRoot, ih]

theorem write_byte_root_from_opening (hash : Bytes → ByteArray) (s : St)
    (depth address : Nat) (capacity : s.pages.size ≤ 2 ^ depth)
    (allocated : address / pageSize < s.pages.size)
    (page : ByteArray) (present : s.pages[address / pageSize]? = some page) (value : UInt8) :
    pageTreeRoot hash (buildPageTree (writeByte s address value).pages depth 0) =
      pageOpeningRoot hash (page.set! (address % pageSize) value)
        (buildPageOpening hash s.pages depth 0 (address / pageSize)) := by
  rw [write_byte_page_tree s depth address capacity allocated page present value,
    built_opening_replacement_root]

end NearCompression
