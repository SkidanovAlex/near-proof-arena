import NearCompression.PageTree

/-! Balanced page trees and numeric index paths. Padding is empty bytes; page
count and chosen depth must be bound by an enclosing memory commitment. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def memoryPageAt (pages : Array ByteArray) (index : Nat) : ByteArray :=
  pages[index]?.getD ByteArray.empty

def buildPageTree (pages : Array ByteArray) : Nat → Nat → PageTree
  | 0, offset => .leaf (memoryPageAt pages offset)
  | depth + 1, offset => .node (buildPageTree pages depth offset)
      (buildPageTree pages depth (offset + 2 ^ depth))

def pageIndexPath : Nat → Nat → List Bool
  | 0, _ => []
  | depth + 1, index =>
    if index < 2 ^ depth then false :: pageIndexPath depth index
    else true :: pageIndexPath depth (index - 2 ^ depth)

theorem page_index_path_length (depth index : Nat) : (pageIndexPath depth index).length = depth := by
  induction depth generalizing index with
  | zero => rfl
  | succ depth ih =>
    simp only [pageIndexPath]
    split <;> simp [ih]

theorem built_page_tree_lookup (pages : Array ByteArray) (depth offset index : Nat)
    (bound : index < 2 ^ depth) :
    pageTreeAt (buildPageTree pages depth offset) (pageIndexPath depth index) =
      some (memoryPageAt pages (offset + index)) := by
  induction depth generalizing offset index with
  | zero =>
    have hi : index = 0 := by simpa using bound
    subst index
    simp [buildPageTree, pageIndexPath, pageTreeAt]
  | succ depth ih =>
    simp only [buildPageTree, pageIndexPath]
    split
    · rename_i h
      change pageTreeAt (buildPageTree pages depth offset) (pageIndexPath depth index) = _
      exact ih offset index h
    · rename_i h
      have hb : index - 2 ^ depth < 2 ^ depth := by
        rw [Nat.pow_succ] at bound
        omega
      change pageTreeAt (buildPageTree pages depth (offset + 2 ^ depth))
        (pageIndexPath depth (index - 2 ^ depth)) = _
      rw [ih _ _ hb]
      congr 2
      omega

theorem memory_page_at_wf (pages : Array ByteArray)
    (wf : ∀ p ∈ pages.toList, bytesWireWf p) (index : Nat) : bytesWireWf (memoryPageAt pages index) := by
  unfold memoryPageAt
  cases he : pages[index]? with
  | none => change 0 < 4294967296; decide +kernel
  | some p => exact wf p (by simpa using (Array.mem_of_getElem? he))

theorem built_page_tree_wf (pages : Array ByteArray)
    (wf : ∀ p ∈ pages.toList, bytesWireWf p) (depth offset : Nat) :
    pageTreeWf (buildPageTree pages depth offset) := by
  induction depth generalizing offset with
  | zero => exact memory_page_at_wf pages wf offset
  | succ depth ih => exact ⟨ih offset, ih (offset + 2 ^ depth)⟩

/-- Numeric page identity is checked through the derived direction sequence.
The root must be supplied by the authenticated enclosing statement. -/
theorem indexed_page_opening_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs))
    (s : St) (depth index : Nat) (capacity : s.pages.size ≤ 2 ^ depth)
    (original : ByteArray) (present : s.pages[index]? = some original)
    (wf : ∀ p ∈ s.pages.toList, bytesWireWf p)
    (page : ByteArray) (pageWf : bytesWireWf page)
    (path : List (Bool × ByteArray)) (pathWf : pageOpeningWf path)
    (directions : path.map Prod.fst = pageIndexPath depth index)
    (accepted : pageTreeRoot hash (buildPageTree s.pages depth 0) = pageOpeningRoot hash page path) :
    original = page ∨ PageCollisionIn hash
      (pageTreeMessages hash (buildPageTree s.pages depth 0)) (pageOpeningMessages hash page path) := by
  have hi : index < s.pages.size := (Array.getElem?_eq_some_iff.mp present).1
  apply page_tree_opening_or_collision hash digestBound _ (built_page_tree_wf s.pages wf depth 0)
    page pageWf path pathWf original _ accepted
  rw [directions, built_page_tree_lookup s.pages depth 0 index (by omega)]
  simp [memoryPageAt, present]

def buildPageOpening (hash : Bytes → ByteArray) (pages : Array ByteArray) :
    Nat → Nat → Nat → List (Bool × ByteArray)
  | 0, _, _ => []
  | depth + 1, offset, index =>
    if index < 2 ^ depth then
      (false, pageTreeRoot hash (buildPageTree pages depth (offset + 2 ^ depth))) ::
        buildPageOpening hash pages depth offset index
    else
      (true, pageTreeRoot hash (buildPageTree pages depth offset)) ::
        buildPageOpening hash pages depth (offset + 2 ^ depth) (index - 2 ^ depth)

theorem built_page_opening_directions (hash : Bytes → ByteArray) (pages : Array ByteArray)
    (depth offset index : Nat) :
    (buildPageOpening hash pages depth offset index).map Prod.fst = pageIndexPath depth index := by
  induction depth generalizing offset index with
  | zero => rfl
  | succ depth ih =>
    simp only [buildPageOpening, pageIndexPath]
    split <;> simp [ih]

theorem built_page_opening_root (hash : Bytes → ByteArray) (pages : Array ByteArray)
    (depth offset index : Nat) (bound : index < 2 ^ depth) :
    pageOpeningRoot hash (memoryPageAt pages (offset + index))
      (buildPageOpening hash pages depth offset index) =
      pageTreeRoot hash (buildPageTree pages depth offset) := by
  induction depth generalizing offset index with
  | zero =>
    have hi : index = 0 := by simpa using bound
    subst index
    simp [buildPageOpening, pageOpeningRoot, buildPageTree, pageTreeRoot]
  | succ depth ih =>
    simp only [buildPageOpening]
    split
    · rename_i h
      simp only [pageOpeningRoot, Bool.false_eq_true, if_false]
      rw [ih offset index h]
      rfl
    · rename_i h
      have hb : index - 2 ^ depth < 2 ^ depth := by
        rw [Nat.pow_succ] at bound
        omega
      have he : offset + index = (offset + 2 ^ depth) + (index - 2 ^ depth) := by omega
      simp only [pageOpeningRoot, if_true]
      rw [he, ih _ _ hb]
      rfl

end NearCompression
