import NearCompression.CachedPageTree

/-! Cache-only witness generation refines the actual-state reference generator. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def cachedPageAt : CachedPageTree → List Bool → Option ByteArray
  | .leaf p _, [] => some p
  | .node l r _, right :: rest => cachedPageAt (if right then r else l) rest
  | _, _ => none

theorem cached_page_at_exact (hash : Bytes → ByteArray) (tree : PageTree) (path : List Bool) :
    cachedPageAt (cachePageTree hash tree) path = pageTreeAt tree path := by
  induction tree generalizing path with
  | leaf p => cases path <;> rfl
  | node l r il ir =>
    cases path with
    | nil => rfl
    | cons direction rest =>
      cases direction <;> simp [cachePageTree, cachedPageAt, pageTreeAt, il, ir]

def cachedBlockSequence (hash : Bytes → ByteArray) (block depth : Nat) :
    CachedPageTree → List BlockBatchPlan → List PageBatchWitness
  | _, [] => []
  | tree, p :: ps =>
    let directions := pageIndexPath depth p.index
    let page := (cachedPageAt tree directions).getD ByteArray.empty
    let witness : PageBatchWitness := ⟨p.index, page, cachedPageOpening tree directions, p.writes⟩
    let next := replaceCachedPageTree (blockTreeHash hash block) tree directions (applyPageWrites page p.writes)
    witness :: cachedBlockSequence hash block depth next ps

theorem cached_block_sequence_exact (hash : Bytes → ByteArray) (block count depth : Nat)
    (positive : 0 < block) (layout : block * count = pageSize)
    (s : St) (full : fullPages s.pages) (capacity : s.pages.size * count ≤ 2 ^ depth)
    (plan : List BlockBatchPlan) (valid : blockPlanValid block (s.pages.size * count) plan) :
    cachedBlockSequence hash block depth
      (cachePageTree (blockTreeHash hash block) (buildSubpageTree s block count depth)) plan =
      honestBlockSequence hash block count depth s plan := by
  induction plan generalizing s with
  | nil => rfl
  | cons p ps ih =>
    have hp := valid p (by simp)
    have lookup : cachedPageAt
        (cachePageTree (blockTreeHash hash block) (buildSubpageTree s block count depth))
        (pageIndexPath depth p.index) = some (memoryPageAt (subpageDirectory s.pages block count) p.index) := by
      rw [cached_page_at_exact]
      unfold buildSubpageTree
      simpa only [Nat.zero_add] using built_page_tree_lookup
        (subpageDirectory s.pages block count) depth 0 p.index (by omega)
    have opening := cached_built_page_opening (blockTreeHash hash block)
      (subpageDirectory s.pages block count) depth 0 p.index
    change cachedPageOpening (cachePageTree (blockTreeHash hash block) (buildSubpageTree s block count depth))
      (pageIndexPath depth p.index) = _ at opening
    simp only [cachedBlockSequence, lookup, Option.getD_some, opening, honestBlockSequence]
    rw [cached_block_batch_update_exact hash s full block count depth p.index positive layout capacity hp.1 p.writes hp.2]
    have tailValid : blockPlanValid block
        ((executeByteRequests s (blockBatchRequests block p.index p.writes)).pages.size * count) ps := by
      rw [execute_byte_requests_page_count]
      intro q hq
      exact valid q (by simp [hq])
    rw [ih _ (execute_requests_full_pages s full _)
      (by simpa only [execute_byte_requests_page_count] using capacity) tailValid]
    rfl

theorem cached_block_sequence_accepted (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs)) (block count depth : Nat)
    (positive : 0 < block) (layout : block * count = pageSize)
    (s : St) (full : fullPages s.pages) (capacity : s.pages.size * count ≤ 2 ^ depth)
    (plan : List BlockBatchPlan) (valid : blockPlanValid block (s.pages.size * count) plan) :
    checkBlockBatches hash (describeSubpageMemory hash s block count depth)
      (cachedBlockSequence hash block depth
        (cachePageTree (blockTreeHash hash block) (buildSubpageTree s block count depth)) plan) =
      some (describeSubpageMemory hash (executeByteRequests s (blockPlanRequests block plan)) block count depth) := by
  rw [cached_block_sequence_exact hash block count depth positive layout s full capacity plan valid]
  exact honest_block_sequence_accepted hash digestBound block count depth positive layout s full capacity plan valid

end NearCompression
