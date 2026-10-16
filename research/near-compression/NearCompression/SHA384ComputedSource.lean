import NearCompression.SHA384PackedSourceBinding
import NearCompression.PackedSourceExecution
namespace NearCompression
open ZkFormal.Algebra

def sha384FpPairWords (pairs : List (Fp×Fp)) : List Nat :=
  pairs.flatMap (fun pair=>[pair.1.toNat,pair.2.toNat])

theorem sha384_fp_pair_words_length (pairs : List (Fp×Fp)) :
    (sha384FpPairWords pairs).length=2*pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih => simp [sha384FpPairWords] at *;omega

theorem sha384_fp_pair_words_canonical (pairs : List (Fp×Fp)) :
    ∀v,v∈sha384FpPairWords pairs → v<2013265921 := by
  intro v hv
  obtain ⟨pair,_,hv⟩ := List.mem_flatMap.mp hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl
  · exact pair.1.toNat_lt
  · exact pair.2.toNat_lt

theorem sha384_fp_pair_words_roundtrip (pairs : List (Fp×Fp)) :
    sha384SourceWordPairs (K:=Fp) (sha384FpPairWords pairs)=pairs := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    have size:=sha384_fp_pair_words_length rest
    unfold sha384SourceWordPairs at ih ⊢
    simp only [sha384FpPairWords,List.flatMap_cons,List.cons_append,List.nil_append,
      List.length_cons] at *
    rw [size]
    have div : (2+(2*rest.length))/2=rest.length+1 := by omega
    rw [show 2*rest.length+1+1=2+(2*rest.length) by omega,div,List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Function.comp_def]
    change (Fp.ofNat pair.1.toNat,Fp.ofNat pair.2.toNat)::_=pair::rest
    rw [Fp.ofNat_toNat,Fp.ofNat_toNat]
    congr 1
    have ih' := ih
    rw [size] at ih'
    simp only [Nat.mul_div_cancel_left _ (by omega : 0<2)] at ih'
    apply Eq.trans ?_ ih'
    apply List.map_congr_left
    intro i hi
    have even : 2*(i+1)=2*i+2 := by omega
    simp only [even,List.getD_cons_succ]

/-- Exactly the canonical base-field word vector stored in a source leaf. -/
def sha384ComputedSourceWords (n p width : Nat) (table : Nat→Nat→Fp)
    (omega : Fp) (index : Nat) : List Nat :=
  sha384FpPairWords (packedComputedWideLeaf n p width table omega index)

theorem sha384_computed_source_decodes (n p width : Nat) (table : Nat→Nat→Fp)
    (omega : Fp) (halfOrder : omega^(2^(n+p+1))= -1)
    (index : Nat) (bound : index<2^(n+p+1)) :
    sha384SourceWordPairs (K:=Fp) (sha384ComputedSourceWords n p width table omega index)=
      sourceWideLeaf (packedComputedSources n p width table) (omega^index) := by
  rw [sha384ComputedSourceWords,sha384_fp_pair_words_roundtrip]
  exact packed_computed_wide_leaf n p width table omega halfOrder index bound
def sha384ComputedSource (n p width : Nat) (table : Nat→Nat→Fp) (omega : Fp) : List (List Nat) :=
  (List.range (2^(n+p+1))).map (sha384ComputedSourceWords n p width table omega)

/-- Eliminates the received-leaf/source semantic equality premise: successful
byte authentication to the modeled computed source gives its actual polynomial
pair, or a collision on the received/constructed path query supports. -/
theorem sha384_authenticated_computed_source (hash : SHA384ByteHash)
    (hashWidth : ∀m,(hash m).length=48) (context : List UInt8)
    (n p width : Nat) (table : Nat→Nat→Fp) (omega : Fp)
    (halfOrder : omega^(2^(n+p+1))= -1) (capacity : 2^(n+p+1)<2^64)
    (lanesBound : (width+2^p-1)/2^p≤64) (index : Nat) (bound : index<2^(n+p+1))
    (contextBound : context.length<2^64) (claimed : List Nat)
    (canonical : ∀v,v∈claimed → v<2013265921) (path : List (List UInt8))
    (accepted : sha384VerifyPath hash
      (sha384SourceRoot hash context ((sha384ComputedSource n p width table omega).map sha384FieldWords) (n+p+1))
      context (2^(n+p+1)) index (sha384FieldWords claimed) path=true) :
    sha384SourceWordPairs (K:=Fp) claimed=sourceWideLeaf (packedComputedSources n p width table) (omega^index) ∨
      ∃a,a∈sha384MerklePathQueries hash context (2^(n+p+1)) index (sha384FieldWords claimed) path ∧
        ∃b,b∈sha384MerklePathQueries hash context (2^(n+p+1)) index
          (sha384FieldWords (sha384ComputedSourceWords n p width table omega index))
          (sha384TreePath hash context ((sha384ComputedSource n p width table omega).map sha384FieldWords) (n+p+1) 0 index) ∧
          a≠b ∧ hash a=hash b := by
  have sourceLength : (sha384ComputedSource n p width table omega).length=2^(n+p+1) := by simp [sha384ComputedSource]
  have sourceGet : (sha384ComputedSource n p width table omega).getD index []=
      sha384ComputedSourceWords n p width table omega index := by simp [sha384ComputedSource,List.getD,bound]
  have leafBound : (sha384FieldWords (sha384ComputedSourceWords n p width table omega index)).length<2^64 := by
    rw [sha384_field_words_length,sha384ComputedSourceWords,sha384_fp_pair_words_length]
    simp only [packedComputedWideLeaf,List.length_map,List.length_range]
    omega
  have values:=sha384_fixed_source_words hash hashWidth context (sha384ComputedSource n p width table omega)
    (n+p+1) index (by omega) sourceLength (by simpa only [sourceLength] using capacity)
    (by simpa only [sourceLength] using bound) contextBound
    (by simpa only [sourceGet] using leafBound)
    (by rw [sourceGet];exact sha384_fp_pair_words_canonical _)
    claimed canonical path (by simpa only [sourceLength] using accepted)
  simp only [sourceGet,sourceLength] at values
  rcases values with equal | collision
  · left
    rw [equal]
    exact sha384_computed_source_decodes n p width table omega halfOrder index bound
  · exact Or.inr collision
end NearCompression
