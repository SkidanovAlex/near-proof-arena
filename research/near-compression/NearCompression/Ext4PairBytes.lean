import NearCompression.CanonicalFieldWordBytes
import NearCompression.DiagnosticExt4Embedding
namespace NearCompression
open ZkFormal.Algebra

/-- One scalar pair in Python's flat [1,v,v²,v³] order, left then right.
The certified tower stores the even coefficients in a and odd ones in b. -/
def ext4PairWords (pair : Fp4×Fp4) : List Nat :=
  [pair.1.a.a.toNat,pair.1.b.a.toNat,pair.1.a.b.toNat,pair.1.b.b.toNat,
   pair.2.a.a.toNat,pair.2.b.a.toNat,pair.2.a.b.toNat,pair.2.b.b.toNat]

theorem ext4_pair_words_canonical (pair : Fp4×Fp4) :
    ∀ x∈ext4PairWords pair,x<2013265921 := by
  intro x hx
  simp only [ext4PairWords,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact Fp.toNat_lt _

theorem ext4_pair_words_injective (left right : Fp4×Fp4)
    (same : ext4PairWords left=ext4PairWords right) : left=right := by
  simp only [ext4PairWords,List.cons.injEq] at same
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,_⟩ := same
  apply Prod.ext <;> apply QuadExt.ext <;> apply QuadExt.ext <;> apply Fp.ext <;> assumption

/-- Canonical byte serialization of the actual single-lane terminal pair. -/
def ext4PairBytes (pair : Fp4×Fp4) : List UInt8 :=
  canonicalFieldWordBytes (ext4PairWords pair)

theorem ext4_pair_bytes_length (pair : Fp4×Fp4) : (ext4PairBytes pair).length=32 := by
  rw [ext4PairBytes,canonical_field_word_bytes_length]
  rfl

theorem ext4_pair_bytes_injective (left right : Fp4×Fp4)
    (same : ext4PairBytes left=ext4PairBytes right) : left=right := by
  apply ext4_pair_words_injective
  exact canonical_field_word_bytes_injective _ _ (ext4_pair_words_canonical left)
    (ext4_pair_words_canonical right) same

/-- Whole scalar-pair trees preserve inequality in canonical coordinate form. -/
theorem ext4_pair_word_tree_injective (left right : List (Fp4×Fp4))
    (same : left.map ext4PairWords=right.map ext4PairWords) : left=right := by
  have size : left.length=right.length := by
    have h:=congrArg List.length same
    simpa using h
  apply List.ext_getElem size
  intro i hl hr
  have cell:=congrArg (fun xs => xs.getD i []) same
  simp [List.getD,hl,hr] at cell
  exact ext4_pair_words_injective _ _ cell

/-- Concrete typed-pair binding reduction. Equal byte-tree roots for different
Fp4 pair trees yield unequal hash inputs on constructed path-query supports. -/
theorem ext4_pair_tree_hash_collision (hash : SHA384ByteHash)
    (width : ∀ m,(hash m).length=48) (context : List UInt8)
    (left right : List (Fp4×Fp4)) (depth : Nat)
    (positive : 0<depth) (leftShape : left.length=2^depth)
    (rightShape : right.length=2^depth) (capacity : left.length<2^64)
    (contextBound : context.length<2^64) (different : left≠right)
    (roots : sha384SourceRoot hash context (left.map ext4PairBytes) depth=
      sha384SourceRoot hash context (right.map ext4PairBytes) depth) :
    let lb := left.map ext4PairBytes
    let rb := right.map ext4PairBytes
    ∃ index,index<left.length ∧ lb.getD index []≠rb.getD index [] ∧
      ∃ a,a∈sha384MerklePathQueries hash context left.length index (lb.getD index [])
        (sha384TreePath hash context lb depth 0 index) ∧
      ∃ b,b∈sha384MerklePathQueries hash context left.length index (rb.getD index [])
        (sha384TreePath hash context rb depth 0 index) ∧ a≠b ∧ hash a=hash b := by
  have canonical (tree : List (Fp4×Fp4)) :
      ∀ leaf∈tree.map ext4PairWords,∀ x∈leaf,x<2013265921 := by
    intro leaf member
    obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp member
    exact ext4_pair_words_canonical pair
  have fits (tree : List (Fp4×Fp4)) :
      ∀ leaf∈tree.map ext4PairWords,4*leaf.length<2^64 := by
    intro leaf member
    obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp member
    change 32<2^64
    decide
  have h := canonical_field_tree_hash_collision hash width context
    (left.map ext4PairWords) (right.map ext4PairWords) depth positive
    (by simpa using leftShape) (by simpa using rightShape) (by simpa using capacity)
    contextBound (canonical left) (canonical right) (fits left) (fits right)
    (fun same => different (ext4_pair_word_tree_injective left right same))
    (by simpa only [List.map_map,show canonicalFieldWordBytes ∘ ext4PairWords=ext4PairBytes from rfl] using roots)
  simpa only [List.map_map,show canonicalFieldWordBytes ∘ ext4PairWords=ext4PairBytes from rfl,List.length_map] using h

end NearCompression
