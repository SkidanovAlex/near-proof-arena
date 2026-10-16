import NearCompression.PageCommitment

/-! Binary page-tree openings. Path/shape and digest-size premises are explicit.
This deterministic collision reduction is not quantum extraction. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def pageNodeDomain : Bytes := [110, 101, 97, 114, 112, 114, 111, 111, 102, 45, 110, 111, 100, 101, 45, 118, 49]
def encodePageNode (l r : ByteArray) : Bytes :=
  pageNodeDomain ++ encodeStorageEntryWire (l, r)

theorem page_node_encoding_injective (l r x y : ByteArray)
    (hl : bytesWireWf l) (hr : bytesWireWf r) (hx : bytesWireWf x) (hy : bytesWireWf y)
    (same : encodePageNode l r = encodePageNode x y) : l = x ∧ r = y := by
  have h : encodeStorageEntryWire (l, r) = encodeStorageEntryWire (x, y) :=
    List.append_cancel_left same
  have he := congrArg (fun bs => parseStorageEntryWire (bs ++ [])) h
  rw [storage_entry_wire_roundtrip _ ⟨hl, hr⟩ [],
    storage_entry_wire_roundtrip _ ⟨hx, hy⟩ []] at he
  exact Prod.mk.inj (congrArg Prod.fst (Except.ok.inj he))

inductive PageTree where
  | leaf (page : ByteArray)
  | node (left right : PageTree)

def pageTreeRoot (hash : Bytes → ByteArray) : PageTree → ByteArray
  | .leaf p => hash (encodeMemoryPage p)
  | .node l r => hash (encodePageNode (pageTreeRoot hash l) (pageTreeRoot hash r))

def pageTreeWf : PageTree → Prop
  | .leaf p => bytesWireWf p
  | .node l r => pageTreeWf l ∧ pageTreeWf r

def pageTreeAt : PageTree → List Bool → Option ByteArray
  | .leaf p, [] => some p
  | .node l r, right :: rest => pageTreeAt (if right then r else l) rest
  | _, _ => none

/-- Root-to-leaf path; true selects the right child. -/
def pageOpeningRoot (hash : Bytes → ByteArray) (page : ByteArray) : List (Bool × ByteArray) → ByteArray
  | [] => hash (encodeMemoryPage page)
  | (right, sibling) :: rest =>
    let child := pageOpeningRoot hash page rest
    hash (if right then encodePageNode sibling child else encodePageNode child sibling)

def pageOpeningWf (path : List (Bool × ByteArray)) : Prop :=
  ∀ x ∈ path, bytesWireWf x.2

def pageTreeMessages (hash : Bytes → ByteArray) : PageTree → List Bytes
  | .leaf p => [encodeMemoryPage p]
  | .node l r => encodePageNode (pageTreeRoot hash l) (pageTreeRoot hash r) ::
      (pageTreeMessages hash l ++ pageTreeMessages hash r)

def pageOpeningMessages (hash : Bytes → ByteArray) (page : ByteArray) :
    List (Bool × ByteArray) → List Bytes
  | [] => [encodeMemoryPage page]
  | (right, sibling) :: rest =>
    (if right then encodePageNode sibling (pageOpeningRoot hash page rest)
     else encodePageNode (pageOpeningRoot hash page rest) sibling) ::
      pageOpeningMessages hash page rest

def PageCollisionIn (hash : Bytes → ByteArray) (reference opening : List Bytes) : Prop :=
  ∃ m ∈ reference, ∃ n ∈ opening, m ≠ n ∧ hash m = hash n

theorem page_tree_opening_or_collision (hash : Bytes → ByteArray)
    (digestBound : ∀ bs, bytesWireWf (hash bs))
    (tree : PageTree) (treeWf : pageTreeWf tree) (page : ByteArray) (pageWf : bytesWireWf page)
    (path : List (Bool × ByteArray)) (pathWf : pageOpeningWf path)
    (original : ByteArray) (lookup : pageTreeAt tree (path.map Prod.fst) = some original)
    (accepted : pageTreeRoot hash tree = pageOpeningRoot hash page path) :
    original = page ∨ PageCollisionIn hash (pageTreeMessages hash tree) (pageOpeningMessages hash page path) := by
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
      · exact Or.inl (memory_page_encoding_injective p page treeWf pageWf same)
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
          · exact Or.inl he
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
          · exact Or.inl he
          · obtain ⟨m, hm, n, hn, hne, heq⟩ := hcol
            exact Or.inr ⟨m, List.mem_cons_of_mem _ (List.mem_append_right _ hm),
              n, List.mem_cons_of_mem _ hn, hne, heq⟩
        · exact Or.inr ⟨_, List.mem_cons_self, _, List.mem_cons_self, same, hh⟩

/-- One leaf hash plus one internal hash for every supplied sibling. -/
theorem page_opening_message_count (hash : Bytes → ByteArray) (page : ByteArray)
    (path : List (Bool × ByteArray)) :
    (pageOpeningMessages hash page path).length = path.length + 1 := by
  induction path with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨right, sibling⟩
    simpa only [pageOpeningMessages, List.length_cons, ih] using
      (Nat.add_right_comm xs.length 1 1)

end NearCompression
