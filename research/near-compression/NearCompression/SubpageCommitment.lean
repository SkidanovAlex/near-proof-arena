import NearCompression.SubpageBounds

/-! Domain-separated block-tree read binding against actual Wasm memory.
The protocol differs from the exploratory Python sweep. Metadata binding remains
an enclosing-statement obligation; no quantum extraction is asserted. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def blockTreeDomain : Bytes := [110, 101, 97, 114, 112, 114, 111, 111, 102, 45, 98, 108, 111, 99, 107, 116, 114, 101, 101, 45, 118, 49]
def blockHashMessage (block : Nat) (message : Bytes) : Bytes := blockTreeDomain ++ u128 block ++ message
def blockTreeHash (hash : Bytes → ByteArray) (block : Nat) (message : Bytes) : ByteArray :=
  hash (blockHashMessage block message)

theorem block_hash_collision_lift (hash : Bytes → ByteArray) (block : Nat) (reference opening : List Bytes)
    (collision : PageCollisionIn (blockTreeHash hash block) reference opening) :
    PageCollisionIn hash (reference.map (blockHashMessage block)) (opening.map (blockHashMessage block)) := by
  obtain ⟨m, hm, n, hn, different, same⟩ := collision
  refine ⟨blockHashMessage block m, List.mem_map.mpr ⟨m, hm, rfl⟩,
    blockHashMessage block n, List.mem_map.mpr ⟨n, hn, rfl⟩, ?_, same⟩
  intro he
  exact different (List.append_cancel_left he)

def buildSubpageTree (s : St) (block count depth : Nat) : PageTree :=
  buildPageTree (subpageDirectory s.pages block count) depth 0

theorem subpage_committed_read_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (s : St) (full : fullPages s.pages)
    (block count depth address : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (capacity : s.pages.size * count ≤ 2 ^ depth) (allocated : address / pageSize < s.pages.size)
    (claimed : ByteArray) (claimWf : bytesWireWf claimed)
    (path : List (Bool × ByteArray)) (pathWf : pageOpeningWf path)
    (directions : path.map Prod.fst = pageIndexPath depth (address / block))
    (accepted : pageTreeRoot (blockTreeHash hash block) (buildSubpageTree s block count depth) =
      pageOpeningRoot (blockTreeHash hash block) claimed path) :
    readByte s address = claimed[address % block]! ∨
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
  rcases page_tree_opening_or_collision (blockTreeHash hash block) (fun bs => digestBound _) _ treeWf
    claimed claimWf path pathWf fragment lookup accepted with same | collision
  · apply Or.inl
    rw [← same]
    have he := wasm_read_subpage s address page present pageFull block count positive layout
    rw [global_block_byte_offset _ _ _ layout] at he
    exact he
  · exact Or.inr (block_hash_collision_lift hash block _ _ collision)

end NearCompression
