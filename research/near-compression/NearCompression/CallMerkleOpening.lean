import NearCompression.CanonicalFieldWordBytes
import NearCompression.GKRPrivateVectorGlue
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

/-- A collision on the claimed path and the fixed source's constructed path.
This records finite query supports rather than assuming global hash injectivity. -/
def CallSourceCollision (hash : SHA384ByteHash) (context : List UInt8)
    (source : List (List Nat)) (depth index : Nat) (claimed : List Nat)
    (path : List (List UInt8)) : Prop :=
  ∃ a,a∈sha384MerklePathQueries hash context source.length index (canonicalFieldWordBytes claimed) path ∧
    ∃ b,b∈sha384MerklePathQueries hash context source.length index
      (canonicalFieldWordBytes (source.getD index []))
      (sha384TreePath hash context (source.map canonicalFieldWordBytes) depth 0 index) ∧
      a≠b ∧ hash a=hash b

/-- An accepted canonical word opening agrees with a fixed source tree or
exhibits a concrete hash collision. Existence of that tree is NOT inferred
from an arbitrary root, and no low-degree property is inferred from hashing. -/
theorem call_source_words_or_collision (hash : SHA384ByteHash)
    (hashWidth : ∀ m,(hash m).length=48) (context : List UInt8)
    (source : List (List Nat)) (depth index : Nat)
    (positive : 0<depth) (shape : source.length=2^depth)
    (capacity : source.length<2^64) (position : index<source.length)
    (contextBound : context.length<2^64)
    (leafBound : (canonicalFieldWordBytes (source.getD index [])).length<2^64)
    (claimed : List Nat) (path : List (List UInt8))
    (sourceCanonical : ∀ x∈source.getD index [],x<2013265921)
    (claimCanonical : ∀ x∈claimed,x<2013265921)
    (accepted : sha384VerifyPath hash
      (sha384SourceRoot hash context (source.map canonicalFieldWordBytes) depth)
      context source.length index (canonicalFieldWordBytes claimed) path=true) :
    claimed=source.getD index [] ∨ CallSourceCollision hash context source depth index claimed path := by
  have leaf : (source.map canonicalFieldWordBytes).getD index []=
      canonicalFieldWordBytes (source.getD index []) := by
    simp [List.getD,position]
  have actual:=sha384_fixed_source_opening hash hashWidth context (source.map canonicalFieldWordBytes)
    depth index positive (by simpa using shape) (by simpa using capacity) (by simpa using position)
    contextBound (by simpa only [leaf] using leafBound) (canonicalFieldWordBytes claimed) path
    (by simpa using accepted)
  rcases actual with same | collision
  · left
    exact canonical_field_word_bytes_injective claimed _ claimCanonical sourceCanonical (same.trans leaf)
  · right
    simpa only [CallSourceCollision,List.length_map,leaf] using collision

/-- Actual source leaves interleave the two antipodal evaluations per lane.
Weights may be adaptive and zero: this deterministic identity needs neither
independence nor division by a challenge. -/
def callPairedSourceValue {K : Type} [Field K] (embed : Nat→K)
    (words : List Nat) (weights : List K) (side : Nat) : K :=
  ((List.range weights.length).map (fun j=>weights.getD j 0*embed (words.getD (2*j+side) 0))).sum

theorem call_source_pair_or_collision {K : Type} [Field K] (embed : Nat→K)
    (weights : List K) (hash : SHA384ByteHash)
    (hashWidth : ∀ m,(hash m).length=48) (context : List UInt8)
    (source : List (List Nat)) (depth index : Nat)
    (positive : 0<depth) (shape : source.length=2^depth)
    (capacity : source.length<2^64) (position : index<source.length)
    (contextBound : context.length<2^64)
    (leafBound : (canonicalFieldWordBytes (source.getD index [])).length<2^64)
    (claimed : List Nat) (path : List (List UInt8))
    (sourceCanonical : ∀ x∈source.getD index [],x<2013265921)
    (claimCanonical : ∀ x∈claimed,x<2013265921)
    (accepted : sha384VerifyPath hash
      (sha384SourceRoot hash context (source.map canonicalFieldWordBytes) depth)
      context source.length index (canonicalFieldWordBytes claimed) path=true) :
    (∀ side,callPairedSourceValue embed claimed weights side=
      callPairedSourceValue embed (source.getD index []) weights side) ∨
    CallSourceCollision hash context source depth index claimed path := by
  rcases call_source_words_or_collision hash hashWidth context source depth index positive shape capacity
    position contextBound leafBound claimed path sourceCanonical claimCanonical accepted with same | collision
  · left;intro side;rw [same]
  · exact Or.inr collision
end NearCompression
