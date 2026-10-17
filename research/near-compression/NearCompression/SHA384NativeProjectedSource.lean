import NearCompression.SHA384NativePackedSource
namespace NearCompression
open ZkFormal.Algebra

/-- Reinterpret canonical base-field words in the challenge field. This is a
word conversion, not an asserted field homomorphism for arbitrary K. -/
def sha384WordLiftFpPairs {K : Type} [Lean.Grind.Field K] (pairs : List (Fp×Fp)) : List (K×K) :=
  pairs.map (fun pair=>(@Nat.cast K Lean.Grind.Semiring.natCast pair.1.toNat,
    @Nat.cast K Lean.Grind.Semiring.natCast pair.2.toNat))

theorem sha384_word_pairs_lift {K : Type} [Lean.Grind.Field K] (words : List Nat)
    (canonical : ∀v,v∈words → v<2013265921) :
    sha384SourceWordPairs (K:=K) words=
      sha384WordLiftFpPairs (sha384SourceWordPairs (K:=Fp) words) := by
  unfold sha384SourceWordPairs sha384WordLiftFpPairs
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  have ib : i<words.length/2 := List.mem_range.mp hi
  have even : 2*i<words.length := by omega
  have odd : 2*i+1<words.length := by omega
  have eb : words.getD (2*i) 0<2013265921 := canonical _ (by simp [List.getD,even])
  have ob : words.getD (2*i+1) 0<2013265921 := canonical _ (by simp [List.getD,odd])
  change _ = (@Nat.cast K Lean.Grind.Semiring.natCast (Fp.ofNat (words.getD (2*i) 0)).toNat,
    @Nat.cast K Lean.Grind.Semiring.natCast (Fp.ofNat (words.getD (2*i+1) 0)).toNat)
  simp only [Fp.toNat_ofNat]
  change words.getD (2*i) 0<P at eb
  change words.getD (2*i+1) 0<P at ob
  rw [Nat.mod_eq_of_lt eb,Nat.mod_eq_of_lt ob]

/-- Actual joint-PCS source index and plus/minus side projection, for arbitrary
verifier-derived challenge-field beta. The result authenticates canonical word
conversion of the computed Fp oracle. Equality to polynomial evaluation in K
requires the separate characteristic/embedding/evaluation bridge. -/
theorem sha384_native_projected_word_pair {K : Type} [Lean.Grind.Field K]
    (beta : List K) (lift sample : Nat) (hash : SHA384ByteHash)
    (hashWidth : ∀m,(hash m).length=48) 
    (n p width : Nat) (table : Nat→Nat→Fp) (fits : SHA384PackingFits n width p)
    (lanesBound : (width+2^p-1)/2^p≤64)
    (claimed : List Nat)
    (canonical : ∀v,v∈claimed → v<2013265921) (path : List (List UInt8))
    (accepted : sha384VerifyPath hash
      (sha384SourceRoot hash (sha384PackingContext n width p) ((sha384ComputedSource n p width table (nativeBabyBearRoot (n+p+2))).map sha384FieldWords) (n+p+1))
      (sha384PackingContext n width p) (2^(n+p+1)) (sample%(2*2^(n+p))) (sha384FieldWords claimed) path=true) :
    projectedBetaPair lift (2^(n+p)) sample beta (sha384SourceWordPairs (K:=K) claimed)=
      projectedBetaPair lift (2^(n+p)) sample beta
        (sha384WordLiftFpPairs (sourceWideLeaf (packedComputedSources n p width table) ((nativeBabyBearRoot (n+p+2))^(sample%(2*2^(n+p)))))) ∨
      ∃a,a∈sha384MerklePathQueries hash (sha384PackingContext n width p) (2^(n+p+1)) (sample%(2*2^(n+p))) (sha384FieldWords claimed) path ∧
        ∃b,b∈sha384MerklePathQueries hash (sha384PackingContext n width p) (2^(n+p+1)) (sample%(2*2^(n+p)))
          (sha384FieldWords (sha384ComputedSourceWords n p width table (nativeBabyBearRoot (n+p+2)) (sample%(2*2^(n+p)))))
          (sha384TreePath hash (sha384PackingContext n width p) ((sha384ComputedSource n p width table (nativeBabyBearRoot (n+p+2))).map sha384FieldWords) (n+p+1) 0 (sample%(2*2^(n+p)))) ∧
          a≠b ∧ hash a=hash b := by
  have shape : 2*2^(n+p)=2^(n+p+1) := by rw [Nat.pow_succ];omega
  have bound : sample%(2*2^(n+p))<2^(n+p+1) := by
    rw [shape]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have result := sha384_authenticated_native_packed_source hash hashWidth n p width table fits lanesBound
    (sample%(2*2^(n+p))) bound claimed canonical path accepted
  rcases result with equal | collision
  · left
    rw [sha384_word_pairs_lift claimed canonical,equal]
  · exact Or.inr collision
end NearCompression
