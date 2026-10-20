import NearCompression.GKRChallengeBlock
namespace NearCompression
open Lean.Grind ArenaCore.Security ZkFormal.Algebra
variable {K : Type} [Field K]

/-- A fixed strategy at a layer boundary. Axis messages depend on past
coordinates only, and terminal a/b are fixed before the fresh gamma. The
strategy may be selected using the complete history of earlier layers. -/
structure GKRLayerStrategy (K : Type) [Field K] (m : Nat) where
  values : Nat → K
  gates : List (GKRWiringGate × K)
  leftBounds : ∀ item∈gates,item.1.left<2^m
  rightBounds : ∀ item∈gates,item.1.right<2^m
  sentLeft : List K → Poly K
  claimLeft : List K → K
  sentRight : List K → List K → Poly K
  claimRight : List K → List K → K
  a : List K → List K → K
  b : List K → List K → K

def GKRLayerStrategy.wrong {m : Nat} (s : GKRLayerStrategy K m) : Prop :=
  s.claimLeft []≠(s.gates.map (fun item => item.2*gkrGateValue item.1.op
    (s.values item.1.left) (s.values item.1.right))).sum

def GKRLayerStrategy.repair {m : Nat} (s : GKRLayerStrategy K m)
    (block : List K × List K × K) : Prop :=
  s.wrong ∧ gkrLayerRepair m s.values s.gates s.sentLeft s.claimLeft
    s.sentRight s.claimRight s.a s.b block.1 block.2.1 block.2.2

/-- Unconditional per-history bound: if the incoming claim is correct the
false-to-true repair event is empty; otherwise use the actual layer bound. -/
theorem gkr_strategy_repair_bound (sample : List K) (distinct : sample.Nodup)
    (m : Nat) (s : GKRLayerStrategy K m) :
    count (gkrChallengeBlocks sample m) s.repair*sample.length≤
      (4*m+1)*(gkrChallengeBlocks sample m).length := by
  classical
  by_cases wrong : s.wrong
  · have mono : count (gkrChallengeBlocks sample m) s.repair≤
        count (gkrChallengeBlocks sample m) (fun block =>
          gkrLayerRepair m s.values s.gates s.sentLeft s.claimLeft s.sentRight
            s.claimRight s.a s.b block.1 block.2.1 block.2.2) :=
      count_mono _ (by intro block repair;exact repair.2)
    exact Nat.le_trans (Nat.mul_le_mul_right sample.length mono)
      (gkr_challenge_block_repair sample distinct m s.values s.gates s.leftBounds
        s.rightBounds s.sentLeft s.claimLeft s.sentRight s.claimRight s.a s.b wrong)
  · have zero : count (gkrChallengeBlocks sample m) s.repair=0 := by
      simp [count,GKRLayerStrategy.repair,wrong]
    rw [zero]
    simp
end NearCompression
