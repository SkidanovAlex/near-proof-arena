import NearCompression.WriteBytesBridge

/-! Ordered writes within one page share one authentication path. No reordering
across pages or host observations is justified by this module. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def applyPageWrites : ByteArray → List (Nat × UInt8) → ByteArray
  | page, [] => page
  | page, (offset, value) :: rest => applyPageWrites (page.set! offset value) rest

def pageBatchRequests (index : Nat) (writes : List (Nat × UInt8)) : List (Nat × UInt8) :=
  writes.map (fun w => (index * pageSize + w.1, w.2))

def pageBatchState (s : St) (index : Nat) (writes : List (Nat × UInt8)) : St :=
  { s with pages := s.pages.modify index (fun p => applyPageWrites p writes) }

def pageBatchFits (writes : List (Nat × UInt8)) : Prop := ∀ w ∈ writes, w.1 < pageSize

theorem page_array_modify_id (pages : Array ByteArray) (index : Nat) :
    pages.modify index id = pages := by
  apply Array.ext
  · simp
  · intro j hj hk
    simp [Array.getElem_modify]

theorem page_array_modify_comp (pages : Array ByteArray) (index : Nat)
    (f g : ByteArray → ByteArray) :
    (pages.modify index f).modify index g = pages.modify index (fun p => g (f p)) := by
  apply Array.ext
  · simp
  · intro j hj hk
    by_cases he : index = j <;> simp [Array.getElem_modify, he]

theorem page_batch_execution_exact (s : St) (index : Nat) (writes : List (Nat × UInt8))
    (fits : pageBatchFits writes) :
    executeByteRequests s (pageBatchRequests index writes) = pageBatchState s index writes := by
  induction writes generalizing s with
  | nil =>
    simp only [executeByteRequests, pageBatchRequests, List.map_nil, List.foldl_nil,
      pageBatchState, applyPageWrites]
    rw [show (fun p : ByteArray => p) = id from rfl, page_array_modify_id]
  | cons w ws ih =>
    obtain ⟨offset, value⟩ := w
    have hb := fits (offset, value) (by simp)
    have hdiv : (index * pageSize + offset) / pageSize = index := by
      simp only [pageSize] at hb ⊢; omega
    have hmod : (index * pageSize + offset) % pageSize = offset := by
      simp only [pageSize] at hb ⊢; omega
    change executeByteRequests (writeByte s (index * pageSize + offset) value)
      (pageBatchRequests index ws) = _
    rw [ih _ (fun w hw => fits w (by simp [hw]))]
    simp only [pageBatchState, writeByte, hdiv, hmod, applyPageWrites]
    rw [page_array_modify_comp]

theorem apply_page_writes_wf (page : ByteArray) (wf : bytesWireWf page)
    (writes : List (Nat × UInt8)) : bytesWireWf (applyPageWrites page writes) := by
  induction writes generalizing page with
  | nil => exact wf
  | cons w ws ih => exact ih _ (bytes_wire_wf_set page wf w.1 w.2)

theorem page_batch_tree (s : St) (depth index : Nat) (capacity : s.pages.size ≤ 2 ^ depth)
    (allocated : index < s.pages.size) (page : ByteArray) (present : s.pages[index]? = some page)
    (writes : List (Nat × UInt8)) :
    buildPageTree (pageBatchState s index writes).pages depth 0 =
      replacePageTree (buildPageTree s.pages depth 0) (pageIndexPath depth index)
        (applyPageWrites page writes) := by
  have h := build_page_tree_modify_inside s.pages depth 0 index
    (fun p => applyPageWrites p writes) (by omega) (by omega)
  simpa [pageBatchState, memoryPageAt, present] using h

def checkPageBatch (hash : Bytes → ByteArray) (d : MemoryDescriptor) (index : Nat)
    (page : ByteArray) (path : List (Bool × ByteArray)) (writes : List (Nat × UInt8)) : Option MemoryDescriptor :=
  if writes.all (fun w => decide (w.1 < pageSize)) && checkMemoryPage hash d index page path then
    some { d with root := pageOpeningRoot hash (applyPageWrites page writes) path }
  else none

theorem checked_page_batch_correct_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (s : St) (depth index : Nat)
    (pagesWf : memoryPagesWf s) (page : ByteArray) (pageWf : bytesWireWf page)
    (path : List (Bool × ByteArray)) (pathWf : pageOpeningWf path)
    (writes : List (Nat × UInt8)) (output : MemoryDescriptor)
    (accepted : checkPageBatch hash (describeMemory hash s depth) index page path writes = some output) :
    output = describeMemory hash (executeByteRequests s (pageBatchRequests index writes)) depth ∨
    PageCollisionIn hash (pageTreeMessages hash (buildPageTree s.pages depth 0))
      (pageOpeningMessages hash page path) := by
  unfold checkPageBatch at accepted
  split at accepted
  · rename_i passed
    have hp : writes.all (fun w => decide (w.1 < pageSize)) = true ∧
        checkMemoryPage hash (describeMemory hash s depth) index page path = true := by
      simpa only [Bool.and_eq_true] using passed
    obtain ⟨fits, opening⟩ := hp
    have fits' : pageBatchFits writes := by simpa [List.all_eq_true, pageBatchFits] using fits
    obtain ⟨hi, capacity, directions, root⟩ := (check_memory_page_correct _ _ _ _ _).mp opening
    change index < s.pages.size at hi
    change s.pages.size ≤ 2 ^ depth at capacity
    change path.map Prod.fst = pageIndexPath depth index at directions
    let original := s.pages[index]
    have present : s.pages[index]? = some original := by simp [original, hi]
    have lookup : pageTreeAt (buildPageTree s.pages depth 0) (path.map Prod.fst) = some original := by
      rw [directions, built_page_tree_lookup s.pages depth 0 index (by omega)]
      simp [memoryPageAt, present]
    rcases page_tree_update_or_collision hash digestBound _ (built_page_tree_wf s.pages pagesWf depth 0)
      page pageWf path pathWf (applyPageWrites page writes) original lookup root with he | hc
    · apply Or.inl
      have hout := (Option.some.inj accepted).symm
      rw [hout, page_batch_execution_exact s index writes fits']
      have hroot : pageTreeRoot hash (buildPageTree (pageBatchState s index writes).pages depth 0) =
          pageOpeningRoot hash (applyPageWrites page writes) path := by
        rw [page_batch_tree s depth index capacity hi original present writes, he.1, ← directions]
        exact he.2
      change MemoryDescriptor.mk s.pages.size depth (pageOpeningRoot hash (applyPageWrites page writes) path) =
        MemoryDescriptor.mk (pageBatchState s index writes).pages.size depth
          (pageTreeRoot hash (buildPageTree (pageBatchState s index writes).pages depth 0))
      rw [hroot]
      simp only [pageBatchState, Array.size_modify]
    · exact Or.inr hc
  · contradiction

end NearCompression
