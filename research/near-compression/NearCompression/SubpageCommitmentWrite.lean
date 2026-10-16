import NearCompression.SubpageCommitment

/-! Committed subpage updates refine the actual Wasm byte writer. Allocation,
layout and tree shape are still supplied by the enclosing statement. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

theorem subpage_tree_write_exact (s : St) (address : Nat) (page : ByteArray)
    (present : s.pages[address / pageSize]? = some page) (full : page.size = pageSize)
    (block count depth : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (capacity : s.pages.size * count ≤ 2 ^ depth) (value : UInt8) :
    buildSubpageTree (writeByte s address value) block count depth =
      replacePageTree (buildSubpageTree s block count depth) (pageIndexPath depth (address / block))
        ((extractSubpage page block (address % pageSize)).set! (address % block) value) := by
  have hi := global_block_allocated s.pages address block count layout (Array.getElem?_eq_some_iff.mp present).1
  have directory : (subpageDirectory s.pages block count)[address / block]? =
      some (extractSubpage page block (address % pageSize)) := by
    rw [subpage_directory_lookup _ _ _ _ hi, global_subpage_lookup _ _ _ _ layout page present]
    rfl
  unfold buildSubpageTree
  rw [subpage_directory_write_exact s address page present full block count positive layout value]
  have hb : address / block < (subpageDirectory s.pages block count).size := by
    simpa [subpageDirectory] using hi
  have h := build_page_tree_modify_inside (subpageDirectory s.pages block count) depth 0 (address / block)
    (fun p => p.set! (address % block) value) (by omega) (by simpa using hb)
  simpa only [Nat.zero_add, memoryPageAt, directory, Option.getD_some] using h

theorem subpage_committed_write_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (s : St) (full : fullPages s.pages)
    (block count depth address : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (capacity : s.pages.size * count ≤ 2 ^ depth) (allocated : address / pageSize < s.pages.size)
    (claimed : ByteArray) (claimWf : bytesWireWf claimed)
    (path : List (Bool × ByteArray)) (pathWf : pageOpeningWf path)
    (directions : path.map Prod.fst = pageIndexPath depth (address / block))
    (accepted : pageTreeRoot (blockTreeHash hash block) (buildSubpageTree s block count depth) =
      pageOpeningRoot (blockTreeHash hash block) claimed path) (value : UInt8) :
    pageTreeRoot (blockTreeHash hash block) (buildSubpageTree (writeByte s address value) block count depth) =
      pageOpeningRoot (blockTreeHash hash block) (claimed.set! (address % block) value) path ∨
    PageCollisionIn hash
      ((pageTreeMessages (blockTreeHash hash block) (buildSubpageTree s block count depth)).map (blockHashMessage block))
      ((pageOpeningMessages (blockTreeHash hash block) claimed path).map (blockHashMessage block)) := by
  let page := s.pages[address / pageSize]
  have present : s.pages[address / pageSize]? = some page := by simp [page, allocated]
  have pageFull : page.size = pageSize := full page (by simp [page])
  let fragment := extractSubpage page block (address % pageSize)
  have hi := global_block_allocated s.pages address block count layout allocated
  have directory : (subpageDirectory s.pages block count)[address / block]? = some fragment := by
    rw [subpage_directory_lookup _ _ _ _ hi, global_subpage_lookup _ _ _ _ layout page present]
    rfl
  have lookup : pageTreeAt (buildSubpageTree s block count depth) (path.map Prod.fst) = some fragment := by
    rw [directions]
    unfold buildSubpageTree
    rw [built_page_tree_lookup _ depth 0 (address / block) (by omega)]
    simp only [memoryPageAt, Nat.zero_add, directory, Option.getD_some]
  have treeWf : pageTreeWf (buildSubpageTree s block count depth) :=
    built_page_tree_wf _ (subpage_directory_wire_wf s.pages full block count layout) depth 0
  rcases page_tree_update_or_collision (blockTreeHash hash block) (fun bs => digestBound _) _ treeWf
    claimed claimWf path pathWf (claimed.set! (address % block) value) fragment lookup accepted with he | hc
  · apply Or.inl
    rw [subpage_tree_write_exact s address page present pageFull block count depth positive layout capacity value]
    change pageTreeRoot (blockTreeHash hash block)
      (replacePageTree (buildSubpageTree s block count depth) (pageIndexPath depth (address / block))
        (fragment.set! (address % block) value)) = _
    rw [he.1, ← directions]
    exact he.2
  · exact Or.inr (block_hash_collision_lift hash block _ _ hc)

end NearCompression
