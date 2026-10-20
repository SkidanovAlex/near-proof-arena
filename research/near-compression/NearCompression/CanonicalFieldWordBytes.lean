import NearCompression.SHA384MerkleSource
namespace NearCompression
open NearSpec

/-- Python field_words writes each canonical BabyBear coordinate as u32 LE. -/
def canonicalFieldWordBytes (words : List Nat) : Bytes :=
  words.flatMap (leN 4)

def readCanonicalWordCount : Nat → Parser (List Nat)
  | 0 => fun bytes => some ([],bytes)
  | n+1 => fun bytes => do
      let (word,rest) ← readLE 4 bytes
      let (words,rest) ← readCanonicalWordCount n rest
      pure (word::words,rest)

theorem canonical_field_word_bytes_length (words : List Nat) :
    (canonicalFieldWordBytes words).length=4*words.length := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    simp only [canonicalFieldWordBytes,List.flatMap_cons,List.length_append,
      leN_length,List.length_cons] at ih ⊢
    omega

/-- Prefix decoding recovers every bounded u32 and leaves the suffix intact.
Canonical field bounds imply these u32 bounds, without modular reduction. -/
theorem canonical_field_words_read_append (words : List Nat) (rest : Bytes)
    (bounded : ∀ word∈words,word<2^32) :
    readCanonicalWordCount words.length (canonicalFieldWordBytes words++rest)=some (words,rest) := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    have head : word<256^4 := bounded word (by simp)
    have tail := ih (fun x hx => bounded x (by simp [hx]))
    simp only [canonicalFieldWordBytes,List.flatMap_cons,List.length_cons,
      List.append_assoc,readCanonicalWordCount]
    rw [readLE_append 4 word _ head]
    dsimp only [Bind.bind,Option.bind]
    unfold canonicalFieldWordBytes at tail
    rw [tail]
    rfl

/-- The actual canonical coordinate restriction prevents serialization aliases,
including aliases between lists of different lengths. -/
theorem canonical_field_word_bytes_injective (left right : List Nat)
    (leftCanonical : ∀ x∈left,x<2013265921)
    (rightCanonical : ∀ x∈right,x<2013265921)
    (same : canonicalFieldWordBytes left=canonicalFieldWordBytes right) : left=right := by
  have lengths := congrArg List.length same
  rw [canonical_field_word_bytes_length,canonical_field_word_bytes_length] at lengths
  have size : left.length=right.length := by omega
  have decoded := congrArg (readCanonicalWordCount left.length) same
  have lp := canonical_field_words_read_append left [] (by intro x hx; have h:=leftCanonical x hx; omega)
  have rp := canonical_field_words_read_append right [] (by intro x hx; have h:=rightCanonical x hx; omega)
  simp only [List.append_nil] at lp rp
  rw [lp,size,rp] at decoded
  exact congrArg Prod.fst (Option.some.inj decoded)

/-- Canonical coordinate leaves preserve tree inequality before hashing.
This is word-stream serialization, not a claim about extension arithmetic. -/
theorem canonical_field_word_tree_injective (left right : List (List Nat))
    (leftCanonical : ∀ leaf∈left,∀ x∈leaf,x<2013265921)
    (rightCanonical : ∀ leaf∈right,∀ x∈leaf,x<2013265921)
    (same : left.map canonicalFieldWordBytes=right.map canonicalFieldWordBytes) : left=right := by
  have size : left.length=right.length := by
    have h:=congrArg List.length same
    simpa using h
  apply List.ext_getElem size
  intro i hl hr
  have cell := congrArg (fun leaves => leaves.getD i []) same
  simp [List.getD,hl,hr] at cell
  exact canonical_field_word_bytes_injective left[i] right[i]
    (leftCanonical _ (List.getElem_mem hl)) (rightCanonical _ (List.getElem_mem hr)) cell

/-- Distinct canonical coordinate trees sharing a framed byte-tree root
produce a concrete collision in the finite path-query supports. -/
theorem canonical_field_tree_hash_collision (hash : SHA384ByteHash)
    (width : ∀ m,(hash m).length=48) (context : Bytes)
    (left right : List (List Nat)) (depth : Nat)
    (positive : 0<depth) (leftShape : left.length=2^depth)
    (rightShape : right.length=2^depth) (capacity : left.length<2^64)
    (contextBound : context.length<2^64)
    (leftCanonical : ∀ leaf∈left,∀ x∈leaf,x<2013265921)
    (rightCanonical : ∀ leaf∈right,∀ x∈leaf,x<2013265921)
    (leftBound : ∀ leaf∈left,4*leaf.length<2^64)
    (rightBound : ∀ leaf∈right,4*leaf.length<2^64)
    (different : left≠right)
    (roots : sha384SourceRoot hash context (left.map canonicalFieldWordBytes) depth=
      sha384SourceRoot hash context (right.map canonicalFieldWordBytes) depth) :
    let lb := left.map canonicalFieldWordBytes
    let rb := right.map canonicalFieldWordBytes
    ∃ index,index<left.length ∧ lb.getD index []≠rb.getD index [] ∧
      ∃ a,a∈sha384MerklePathQueries hash context left.length index (lb.getD index [])
        (sha384TreePath hash context lb depth 0 index) ∧
      ∃ b,b∈sha384MerklePathQueries hash context left.length index (rb.getD index [])
        (sha384TreePath hash context rb depth 0 index) ∧ a≠b ∧ hash a=hash b := by
  have bounds (tree : List (List Nat)) (fits : ∀ leaf∈tree,4*leaf.length<2^64)
      (i : Nat) (hi : i<(tree.map canonicalFieldWordBytes).length) :
      ((tree.map canonicalFieldWordBytes).getD i []).length<2^64 := by
    have pos : i<tree.length := by simpa using hi
    simpa [List.getD,pos,canonical_field_word_bytes_length] using fits tree[i] (List.getElem_mem pos)
  have collision := sha384_source_tree_collision hash width context
    (left.map canonicalFieldWordBytes) (right.map canonicalFieldWordBytes) depth positive
    (by simpa using leftShape) (by simpa using rightShape) (by simpa using capacity)
    contextBound (bounds left leftBound) (bounds right rightBound)
    (fun equal => different (canonical_field_word_tree_injective left right leftCanonical rightCanonical equal)) roots
  simpa only [List.length_map] using collision

end NearCompression
