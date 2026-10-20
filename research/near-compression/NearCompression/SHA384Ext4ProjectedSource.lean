import NearCompression.DiagnosticExt4Polynomial
namespace NearCompression
open ZkFormal.Algebra
/-- Authentication to the fixed native computed source now implies genuine
challenge-field source polynomial evaluations, followed by the verifier's
weighted/lifted pair projection. No unknown-root extraction or security bound. -/
theorem sha384_native_ext4_projected_pair (beta : List Fp4) (lift sample : Nat) (hash : SHA384ByteHash)
    (hashWidth : ∀m,(hash m).length=48) 
    (n p width : Nat) (table : Nat→Nat→Fp) (fits : SHA384PackingFits n width p)
    (lanesBound : (width+2^p-1)/2^p≤64)
    (claimed : List Nat)
    (canonical : ∀v,v∈claimed → v<2013265921) (path : List (List UInt8))
    (accepted : sha384VerifyPath hash
      (sha384SourceRoot hash (sha384PackingContext n width p) ((sha384ComputedSource n p width table (nativeBabyBearRoot (n+p+2))).map sha384FieldWords) (n+p+1))
      (sha384PackingContext n width p) (2^(n+p+1)) (sample%(2*2^(n+p))) (sha384FieldWords claimed) path=true) :
    projectedBetaPair lift (2^(n+p)) sample beta (sha384SourceWordPairs (K:=Fp4) claimed)=
      projectedBetaPair lift (2^(n+p)) sample beta
        (sourceWideLeaf (packedComputedSources n p width (fun r c=>diagnosticExt4Embed (table r c)))
          ((diagnosticExt4Root (n+p+2))^(sample%(2*2^(n+p))))) ∨
      ∃a,a∈sha384MerklePathQueries hash (sha384PackingContext n width p) (2^(n+p+1)) (sample%(2*2^(n+p))) (sha384FieldWords claimed) path ∧
        ∃b,b∈sha384MerklePathQueries hash (sha384PackingContext n width p) (2^(n+p+1)) (sample%(2*2^(n+p)))
          (sha384FieldWords (sha384ComputedSourceWords n p width table (nativeBabyBearRoot (n+p+2)) (sample%(2*2^(n+p)))))
          (sha384TreePath hash (sha384PackingContext n width p) ((sha384ComputedSource n p width table (nativeBabyBearRoot (n+p+2))).map sha384FieldWords) (n+p+1) 0 (sample%(2*2^(n+p)))) ∧
          a≠b ∧ hash a=hash b := by
  have result := sha384_native_projected_word_pair beta lift sample hash hashWidth n p width table fits
    lanesBound claimed canonical path accepted
  rcases result with equal | collision
  · left
    rw [diagnostic_ext4_source_pair,diagnostic_ext4_embed_pow] at equal
    exact equal
  · exact Or.inr collision
end NearCompression
