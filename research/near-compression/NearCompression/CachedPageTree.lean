import NearCompression.BlockGrouping

/-! Cached subtree roots with exact correspondence to the reference tree.
Only constructors and updates proved below establish cache consistency. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

inductive CachedPageTree where
  | leaf (page root : ByteArray)
  | node (left right : CachedPageTree) (root : ByteArray)

def cachedPageRoot : CachedPageTree → ByteArray
  | .leaf _ root => root
  | .node _ _ root => root

def cachePageTree (hash : Bytes → ByteArray) : PageTree → CachedPageTree
  | .leaf p => .leaf p (hash (encodeMemoryPage p))
  | .node l r =>
    let left := cachePageTree hash l
    let right := cachePageTree hash r
    .node left right (hash (encodePageNode (cachedPageRoot left) (cachedPageRoot right)))

def replaceCachedPageTree (hash : Bytes → ByteArray) : CachedPageTree → List Bool → ByteArray → CachedPageTree
  | .leaf _ _, [], p => .leaf p (hash (encodeMemoryPage p))
  | .node l r _, false :: rest, p =>
    let left := replaceCachedPageTree hash l rest p
    .node left r (hash (encodePageNode (cachedPageRoot left) (cachedPageRoot r)))
  | .node l r _, true :: rest, p =>
    let right := replaceCachedPageTree hash r rest p
    .node l right (hash (encodePageNode (cachedPageRoot l) (cachedPageRoot right)))
  | tree, _, _ => tree

theorem cached_page_root_exact (hash : Bytes → ByteArray) (tree : PageTree) :
    cachedPageRoot (cachePageTree hash tree) = pageTreeRoot hash tree := by
  induction tree with
  | leaf p => rfl
  | node l r il ir =>
    change hash (encodePageNode (cachedPageRoot (cachePageTree hash l))
      (cachedPageRoot (cachePageTree hash r))) = _
    rw [il, ir]
    rfl

theorem cached_page_replace_exact (hash : Bytes → ByteArray) (tree : PageTree)
    (path : List Bool) (replacement : ByteArray) :
    replaceCachedPageTree hash (cachePageTree hash tree) path replacement =
      cachePageTree hash (replacePageTree tree path replacement) := by
  induction tree generalizing path with
  | leaf p => cases path <;> rfl
  | node l r il ir =>
    cases path with
    | nil => rfl
    | cons direction rest =>
      cases direction <;> simp only [cachePageTree, replaceCachedPageTree, replacePageTree, il, ir]

theorem cached_block_batch_update_exact (hash : Bytes → ByteArray) (s : St) (full : fullPages s.pages)
    (block count depth index : Nat) (positive : 0 < block) (layout : block * count = pageSize)
    (capacity : s.pages.size * count ≤ 2 ^ depth) (allocated : index < s.pages.size * count)
    (writes : List (Nat × UInt8)) (fits : ∀ w ∈ writes, w.1 < block) :
    replaceCachedPageTree (blockTreeHash hash block)
      (cachePageTree (blockTreeHash hash block) (buildSubpageTree s block count depth))
      (pageIndexPath depth index)
      (applyPageWrites (memoryPageAt (subpageDirectory s.pages block count) index) writes) =
      cachePageTree (blockTreeHash hash block)
        (buildSubpageTree (executeByteRequests s (blockBatchRequests block index writes)) block count depth) := by
  rw [cached_page_replace_exact,
    block_batch_tree_exact s full block count depth index positive layout capacity allocated writes fits]

def cachedPageOpening : CachedPageTree → List Bool → List (Bool × ByteArray)
  | .node l r _, false :: rest => (false, cachedPageRoot r) :: cachedPageOpening l rest
  | .node l r _, true :: rest => (true, cachedPageRoot l) :: cachedPageOpening r rest
  | _, _ => []

theorem cached_built_page_opening (hash : Bytes → ByteArray) (pages : Array ByteArray)
    (depth offset index : Nat) :
    cachedPageOpening (cachePageTree hash (buildPageTree pages depth offset)) (pageIndexPath depth index) =
      buildPageOpening hash pages depth offset index := by
  induction depth generalizing offset index with
  | zero => rfl
  | succ depth ih =>
    simp only [buildPageTree, pageIndexPath, buildPageOpening]
    split <;> simp only [cachePageTree, cachedPageOpening, cached_page_root_exact, ih]

end NearCompression
