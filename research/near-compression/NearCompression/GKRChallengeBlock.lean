import NearCompression.AdaptiveLayerBudget
namespace NearCompression
open Lean.Grind ArenaCore.Security ZkFormal.Algebra

/-- One layer draws two m-coordinate axes and then a fresh gamma. -/
def gkrChallengeBlocks {K : Type} (sample : List K) (m : Nat) : List (List K × List K × K) :=
  (uniformTuples sample m).flatMap (fun ru => (uniformTuples sample m).flatMap
    (fun rv => sample.map (fun gamma => (ru,rv,gamma))))

private theorem constant_sum {A : Type} (xs : List A) (n : Nat) :
    (xs.map (fun _ => n)).sum=xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih];grind

theorem gkr_challenge_block_length {K : Type} (sample : List K) (m : Nat) :
    (gkrChallengeBlocks sample m).length=sample.length^(2*m+1) := by
  simp only [gkrChallengeBlocks,List.length_flatMap,List.length_map,constant_sum,
    uniform_tuples_length]
  rw [Nat.pow_succ,show 2*m=m+m by omega,Nat.pow_add]
  grind

theorem gkr_challenge_block_count {K : Type} (sample : List K) (m : Nat)
    (event : List K → List K → K → Prop) :
    count (gkrChallengeBlocks sample m) (fun block => event block.1 block.2.1 block.2.2)=
      ((uniformTuples sample m).map (fun ru => ((uniformTuples sample m).map
        (fun rv => count sample (event ru rv))).sum)).sum := by
  classical
  simp only [count,gkrChallengeBlocks,List.countP_flatMap,List.countP_map,
    Function.comp_def]

variable {K : Type} [Field K]

/-- The existing repair bound expressed as a single challenge block, ready for
causal layer composition. No messages depend on their future challenge block. -/
theorem gkr_challenge_block_repair (sample : List K) (distinct : sample.Nodup) (m : Nat)
    (values : Nat → K) (gates : List (GKRWiringGate × K))
    (leftBounds : ∀ item∈gates,item.1.left<2^m)
    (rightBounds : ∀ item∈gates,item.1.right<2^m)
    (sentLeft : List K → Poly K) (claimLeft : List K → K)
    (sentRight : List K → List K → Poly K) (claimRight : List K → List K → K)
    (a b : List K → List K → K)
    (wrong : claimLeft []≠(gates.map (fun item => item.2*gkrGateValue item.1.op
      (values item.1.left) (values item.1.right))).sum) :
    count (gkrChallengeBlocks sample m) (fun block =>
      gkrLayerRepair m values gates sentLeft claimLeft sentRight claimRight a b
        block.1 block.2.1 block.2.2)*sample.length≤
      (4*m+1)*(gkrChallengeBlocks sample m).length := by
  rw [gkr_challenge_block_count,gkr_challenge_block_length]
  exact gkr_layer_repair_count sample distinct m values gates leftBounds rightBounds
    sentLeft claimLeft sentRight claimRight a b wrong
end NearCompression
