import NearCompression.GKRConcreteErrorInclusion
import NearCompression.GKREarlierJointCount
import NearCompression.LocalBatchedGKR
namespace NearCompression
open ArenaCore.Security

/-- PCS randomness sampled after the complete GKR path. -/
def gkrPCSContinuationSamples {K : Type} (sample : List K) (layout : GKRJointLayout) (queries : Nat) :=
  (uniformTuples sample layout.commonLog).flatMap (fun z =>
    (uniformTuples sample layout.commonLog).flatMap (fun path =>
      (uniformTuples (List.range (4*2^layout.commonLog)) queries).map (fun qs => (z,path,qs))))

/-- The full chronological row/GKR/PCS experiment, before fixing any GKR block. -/
def gkrFullPCSSamples {K : Type} (sample : List K) (layout : GKRJointLayout)
    (earlierRounds : List Nat) (queries : Nat) :=
  (uniformTuples sample layout.rowCoordinates).flatMap (fun rows =>
    (gkrChallengePaths sample (earlierRounds++[layout.inputLog])).flatMap (fun blocks =>
      (gkrPCSContinuationSamples sample layout queries).map (fun tail => (rows,blocks,tail))))

/-- Split off the last GKR block and exchange only finite counting sums.
The predicate still receives the entire original path, so adaptive message
dependencies are preserved, including row-dependent earlier messages. -/
theorem gkr_full_pcs_event_count {K : Type}
    (sample : List K) (layout : GKRJointLayout) (earlierRounds : List Nat) (queries : Nat)
    (event : List K → List (GKRBlock K) → List K → List K → List Nat → Prop) :
    count (gkrFullPCSSamples sample layout earlierRounds queries)
      (fun item => event item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2)=
    ((gkrChallengePaths sample earlierRounds).map (fun earlier =>
      count (gkrConcretePCSSamples sample layout queries) (fun item =>
        event item.1 (earlier++[item.2.1]) item.2.2.1 item.2.2.2.1 item.2.2.2.2))).sum := by
  classical
  unfold gkrFullPCSSamples
  rw [gkr_challenge_paths_append]
  simp only [gkrChallengePaths,List.flatMap_nil,List.flatMap_cons,List.map_nil,List.map_cons,
    List.append_nil,List.flatMap_map,List.flatMap_assoc]
  rw [gkr_finite_sample_exchange]
  simp only [gkrPCSContinuationSamples,gkrConcretePCSSamples,count,List.countP_flatMap,
    List.countP_map,Function.comp_def]

/-- A concrete joint PCS budget for every earlier path lifts with precisely
that path space's multiplicity. Row coordinates are never conditioned away. -/
theorem gkr_full_pcs_event_budget {K : Type}
    (sample : List K) (layout : GKRJointLayout) (earlierRounds : List Nat) (queries : Nat)
    (event : List K → List (GKRBlock K) → List K → List K → List Nat → Prop)
    (scale budget : Nat)
    (joint : ∀ earlier∈gkrChallengePaths sample earlierRounds,
      count (gkrConcretePCSSamples sample layout queries) (fun item =>
        event item.1 (earlier++[item.2.1]) item.2.2.1 item.2.2.2.1 item.2.2.2.2)*scale≤budget) :
    count (gkrFullPCSSamples sample layout earlierRounds queries)
      (fun item => event item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2)*scale≤
      (gkrChallengePaths sample earlierRounds).length*budget := by
  rw [gkr_full_pcs_event_count]
  generalize gkrChallengePaths sample earlierRounds=paths at *
  induction paths with
  | nil => simp
  | cons path paths ih =>
    have head := joint path (by simp)
    have tail := ih (fun p hp => joint p (by simp [hp]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul]
    omega

/-- Exact bridge from the evaluated-GKR continuation experiment used by the
local/batching bound to the full PCS experiment used above. -/
theorem evaluated_gkr_full_pcs_count {K : Type}
    (sample : List K) (layout : GKRJointLayout) (earlierRounds : List Nat) (queries : Nat)
    (event : List K → List (GKRBlock K) → List K → List K → List Nat → Prop) :
    ((uniformTuples sample layout.rowCoordinates).map (fun rows =>
      count (evaluatedGKRExperiment sample (earlierRounds++[layout.inputLog])
        (gkrPCSContinuationSamples sample layout queries))
        (fun pair => event rows pair.1 pair.2.1 pair.2.2.1 pair.2.2.2))).sum=
    count (gkrFullPCSSamples sample layout earlierRounds queries)
      (fun item => event item.1 item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2) := by
  classical
  simp only [evaluatedGKRExperiment,gkrFullPCSSamples,count,List.countP_flatMap,
    List.countP_map,Function.comp_def]

/-- The joint PCS budget now bounds the row-averaged evaluated GKR error
experiment directly, ready for summation over earlier local challenges. -/
theorem evaluated_gkr_joint_pcs_budget {K : Type}
    (sample : List K) (layout : GKRJointLayout) (earlierRounds : List Nat) (queries : Nat)
    (event : List K → List (GKRBlock K) → List K → List K → List Nat → Prop)
    (scale budget : Nat)
    (joint : ∀ earlier∈gkrChallengePaths sample earlierRounds,
      count (gkrConcretePCSSamples sample layout queries) (fun item =>
        event item.1 (earlier++[item.2.1]) item.2.2.1 item.2.2.2.1 item.2.2.2.2)*scale≤budget) :
    ((uniformTuples sample layout.rowCoordinates).map (fun rows =>
      count (evaluatedGKRExperiment sample (earlierRounds++[layout.inputLog])
        (gkrPCSContinuationSamples sample layout queries))
        (fun pair => event rows pair.1 pair.2.1 pair.2.2.1 pair.2.2.2))).sum*scale≤
      (gkrChallengePaths sample earlierRounds).length*budget := by
  rw [evaluated_gkr_full_pcs_count]
  exact gkr_full_pcs_event_budget sample layout earlierRounds queries event scale budget joint

end NearCompression
