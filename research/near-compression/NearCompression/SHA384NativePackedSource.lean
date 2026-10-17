import NearCompression.SHA384ComputedSource
import NearCompression.SHA384PackingContext
namespace NearCompression
open ZkFormal.Algebra

/-- The packed rate-four source uses the certified root; no caller root-order premise. -/
theorem sha384_native_packed_half (n width p : Nat) (fits : SHA384PackingFits n width p) :
    (nativeBabyBearRoot (n+p+2))^(2^(n+p+1))= -1 := by
  rw [native_babybear_root_eq _ fits.2.2.2.2.2]
  have half := Fp.twoAdicGen_pow_half (by omega : 1≤n+p+2) fits.2.2.2.2.2
  simpa only [show n+p+2-1=n+p+1 by omega] using half

/-- Fixed-source authentication with the literal packing context/root formula.
Only byte/path binding is claimed, not extraction from an arbitrary root. -/
theorem sha384_authenticated_native_packed_source (hash : SHA384ByteHash)
    (hashWidth : ∀m,(hash m).length=48) 
    (n p width : Nat) (table : Nat→Nat→Fp) (fits : SHA384PackingFits n width p)
    (lanesBound : (width+2^p-1)/2^p≤64) (index : Nat) (bound : index<2^(n+p+1))
    (claimed : List Nat)
    (canonical : ∀v,v∈claimed → v<2013265921) (path : List (List UInt8))
    (accepted : sha384VerifyPath hash
      (sha384SourceRoot hash (sha384PackingContext n width p) ((sha384ComputedSource n p width table (nativeBabyBearRoot (n+p+2))).map sha384FieldWords) (n+p+1))
      (sha384PackingContext n width p) (2^(n+p+1)) index (sha384FieldWords claimed) path=true) :
    sha384SourceWordPairs (K:=Fp) claimed=sourceWideLeaf (packedComputedSources n p width table) ((nativeBabyBearRoot (n+p+2))^index) ∨
      ∃a,a∈sha384MerklePathQueries hash (sha384PackingContext n width p) (2^(n+p+1)) index (sha384FieldWords claimed) path ∧
        ∃b,b∈sha384MerklePathQueries hash (sha384PackingContext n width p) (2^(n+p+1)) index
          (sha384FieldWords (sha384ComputedSourceWords n p width table (nativeBabyBearRoot (n+p+2)) index))
          (sha384TreePath hash (sha384PackingContext n width p) ((sha384ComputedSource n p width table (nativeBabyBearRoot (n+p+2))).map sha384FieldWords) (n+p+1) 0 index) ∧
          a≠b ∧ hash a=hash b := by
  have capacity : 2^(n+p+1)<2^64 := by
    have le : 2^(n+p+1)≤2^27 := Nat.pow_le_pow_right (by omega) (by have h:=fits.2.2.2.2.2;omega)
    omega
  have contextBound : (sha384PackingContext n width p).length<2^64 := by
    rw [sha384_packing_context_length]
    decide
  exact sha384_authenticated_computed_source hash hashWidth (sha384PackingContext n width p)
    n p width table (nativeBabyBearRoot (n+p+2))
    (sha384_native_packed_half n width p fits) capacity lanesBound index bound contextBound
    claimed canonical path accepted
end NearCompression
