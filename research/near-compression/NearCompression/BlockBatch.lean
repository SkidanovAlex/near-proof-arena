import NearCompression.BlockWriteBytes

/-! Ordered writes within one block refine one directory replacement. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def blockBatchRequests (block index : Nat) (writes : List (Nat × UInt8)) : List (Nat × UInt8) :=
  writes.map (fun w => (index * block + w.1, w.2))

theorem block_batch_directory_exact (s : St) (full : fullPages s.pages)
    (block count index : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (allocated : index < s.pages.size * count) (writes : List (Nat × UInt8))
    (fits : ∀ w ∈ writes, w.1 < block) :
    subpageDirectory (executeByteRequests s (blockBatchRequests block index writes)).pages block count =
      (subpageDirectory s.pages block count).modify index (fun p => applyPageWrites p writes) := by
  induction writes generalizing s with
  | nil =>
    simp only [blockBatchRequests, List.map_nil, executeByteRequests, List.foldl_nil, applyPageWrites]
    exact (page_array_modify_id _ _).symm
  | cons w ws ih =>
    obtain ⟨offset, value⟩ := w
    have hb : offset < block := fits (offset, value) (by simp)
    have hdiv : (index * block + offset) / block = index := by
      simp [Nat.add_div, Nat.div_eq_of_lt hb, positive, Nat.mod_lt _ positive]
    have hmod : (index * block + offset) % block = offset := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hb]
    have pageAllocated : (index * block + offset) / pageSize < s.pages.size := by
      rw [← global_block_page_index _ block count layout, hdiv]
      exact (Nat.div_lt_iff_lt_mul (subpage_count_positive block count layout)).mpr allocated
    let page := s.pages[(index * block + offset) / pageSize]
    have present : s.pages[(index * block + offset) / pageSize]? = some page := by
      simp [page, pageAllocated]
    have pageFull : page.size = pageSize := full page (by simp [page])
    change subpageDirectory
      (executeByteRequests (writeByte s (index * block + offset) value) (blockBatchRequests block index ws)).pages
      block count = _
    rw [ih _ (write_byte_full_pages s full _ _) (by simpa only [writeByte, Array.size_modify] using allocated)
      (fun w hw => fits w (by simp [hw]))]
    rw [subpage_directory_write_exact s _ page present pageFull block count positive layout value, hdiv, hmod]
    rw [page_array_modify_comp]
    rfl

theorem block_batch_tree_exact (s : St) (full : fullPages s.pages)
    (block count depth index : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (capacity : s.pages.size * count ≤ 2 ^ depth) (allocated : index < s.pages.size * count)
    (writes : List (Nat × UInt8)) (fits : ∀ w ∈ writes, w.1 < block) :
    buildSubpageTree (executeByteRequests s (blockBatchRequests block index writes)) block count depth =
      replacePageTree (buildSubpageTree s block count depth) (pageIndexPath depth index)
        (applyPageWrites (memoryPageAt (subpageDirectory s.pages block count) index) writes) := by
  unfold buildSubpageTree
  rw [block_batch_directory_exact s full block count index positive layout allocated writes fits]
  have hi : index < (subpageDirectory s.pages block count).size := by
    simpa [subpageDirectory] using allocated
  simpa only [Nat.zero_add] using build_page_tree_modify_inside
    (subpageDirectory s.pages block count) depth 0 index (fun p => applyPageWrites p writes)
    (by omega) (by simpa using hi)

theorem subpage_batch_root_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (s : St) (full : fullPages s.pages)
    (block count depth index : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (capacity : s.pages.size * count ≤ 2 ^ depth) (allocated : index < s.pages.size * count)
    (writes : List (Nat × UInt8)) (fits : ∀ w ∈ writes, w.1 < block)
    (claimed : ByteArray) (claimWf : bytesWireWf claimed)
    (path : List (Bool × ByteArray)) (pathWf : pageOpeningWf path)
    (directions : path.map Prod.fst = pageIndexPath depth index)
    (accepted : pageTreeRoot (blockTreeHash hash block) (buildSubpageTree s block count depth) =
      pageOpeningRoot (blockTreeHash hash block) claimed path) :
    pageTreeRoot (blockTreeHash hash block)
      (buildSubpageTree (executeByteRequests s (blockBatchRequests block index writes)) block count depth) =
      pageOpeningRoot (blockTreeHash hash block) (applyPageWrites claimed writes) path ∨
    PageCollisionIn hash
      ((pageTreeMessages (blockTreeHash hash block) (buildSubpageTree s block count depth)).map (blockHashMessage block))
      ((pageOpeningMessages (blockTreeHash hash block) claimed path).map (blockHashMessage block)) := by
  let original := memoryPageAt (subpageDirectory s.pages block count) index
  have lookup : pageTreeAt (buildSubpageTree s block count depth) (path.map Prod.fst) = some original := by
    rw [directions]
    unfold buildSubpageTree
    simpa only [Nat.zero_add] using built_page_tree_lookup
      (subpageDirectory s.pages block count) depth 0 index (by omega)
  have treeWf : pageTreeWf (buildSubpageTree s block count depth) :=
    built_page_tree_wf _ (subpage_directory_wire_wf s.pages full block count layout) depth 0
  rcases page_tree_update_or_collision (blockTreeHash hash block) (fun bs => digestBound _) _ treeWf
    claimed claimWf path pathWf (applyPageWrites claimed writes) original lookup accepted with correct | collision
  · apply Or.inl
    rw [block_batch_tree_exact s full block count depth index positive layout capacity allocated writes fits]
    change pageTreeRoot (blockTreeHash hash block)
      (replacePageTree (buildSubpageTree s block count depth) (pageIndexPath depth index)
        (applyPageWrites original writes)) = _
    rw [correct.1, ← directions]
    exact correct.2
  · exact Or.inr (block_hash_collision_lift hash block _ _ collision)

end NearCompression
