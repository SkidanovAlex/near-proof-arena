import NearCompression.GKRCheckedPath
namespace NearCompression
open Lean.Grind ArenaCore.Security
variable {K : Type} [Field K]

def gkrChallengePaths (sample : List K) : List Nat → List (List (GKRBlock K))
  | [] => [[]]
  | m::rest => (gkrChallengeBlocks sample m).flatMap (fun block =>
      (gkrChallengePaths sample rest).map (block::·))

private theorem sum_constant {A : Type} (xs : List A) (n : Nat) :
    (xs.map (fun _ => n)).sum=xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih];grind

theorem gkr_challenge_paths_length (sample : List K) (rounds : List Nat) :
    (gkrChallengePaths sample rounds).length=layerChallengeMass (gkrLayerStages sample rounds) := by
  induction rounds with
  | nil => rfl
  | cons m rest ih =>
    simp only [gkrChallengePaths,List.length_flatMap,List.length_map,sum_constant,ih,
      gkrLayerStages,List.map_cons,layerChallengeMass]

/-- Exact equality between the full path event count and the recursive
first-repair tree, retaining all continuations once an event occurs. -/
theorem gkr_path_repair_count (sample : List K)
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (rounds : List Nat) (history : List (GKRBlock K)) :
    count (gkrChallengePaths sample rounds) (gkrPathRepair strategy history rounds)=
      gkrAdaptiveLayerFailures sample strategy history rounds := by
  classical
  induction rounds generalizing history with
  | nil => simp [gkrChallengePaths,gkrPathRepair,gkrAdaptiveLayerFailures,count]
  | cons m rest ih =>
    simp only [gkrChallengePaths,count,List.countP_flatMap,List.countP_map,
      Function.comp_def,gkrAdaptiveLayerFailures]
    congr 1
    apply List.map_congr_left
    intro block hb
    by_cases repair : (strategy m history).repair block
    · simp only [gkrPathRepair,repair,true_or,decide_true,ite_true,List.countP_true]
      exact gkr_challenge_paths_length sample rest
    · simp only [gkrPathRepair,repair,false_or,ite_false]
      exact ih (history++[block])

/-- Ideal acceptance bound for the explicitly linked checked-path relation.
The relation includes correct terminal input and adjacent semantic linkage;
those must still be derived from a fixed circuit and authenticated PCS claim
before this theorem applies to the cryptographic verifier. -/
theorem gkr_linked_checked_path_budget (sample : List K) (distinct : sample.Nodup)
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (rounds : List Nat) (history : List (GKRBlock K))
    (wrong : ∀ m rest,rounds=m::rest → (strategy m history).wrong) :
    count (gkrChallengePaths sample rounds) (gkrCheckedToInput strategy history rounds)*sample.length≤
      (rounds.map (fun m => 4*m+1)).sum*(gkrChallengePaths sample rounds).length := by
  have subset : count (gkrChallengePaths sample rounds) (gkrCheckedToInput strategy history rounds)≤
      count (gkrChallengePaths sample rounds) (gkrPathRepair strategy history rounds) := by
    apply count_mono
    intro blocks checked
    exact gkr_checked_path_has_repair strategy rounds blocks history checked wrong
  have scaled:=Nat.mul_le_mul_right sample.length subset
  rw [gkr_path_repair_count] at scaled
  rw [gkr_challenge_paths_length]
  exact Nat.le_trans scaled (gkr_adaptive_layers_repair_budget sample distinct strategy rounds history)
end NearCompression
