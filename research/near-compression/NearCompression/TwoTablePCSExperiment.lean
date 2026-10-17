import NearCompression.TableHistoryBinding
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- Randomness after the local table protocols: batching, all GKR blocks,
and then weighted PCS and folding/query draws. -/
def twoTablePCSContinuations {K : Type} (sample : List K) (layout : GKRJointLayout)
    (earlierRounds : List Nat) (queries : Nat) :=
  sample.flatMap (fun rho =>
    (evaluatedGKRExperiment sample (earlierRounds++[layout.inputLog])
      (gkrPCSContinuationSamples sample layout queries)).map (fun x => (rho,x)))

/-- Concrete PCS budgets lift over both local initial challenge families,
batching and earlier GKR paths, while keeping all row coordinates jointly
sampled. The event may depend on every sampled value. -/
theorem two_table_gkr_pcs_joint_budget {K : Type} [Field K]
    (sample : List K) (layout : GKRJointLayout) (firstRows secondRows : Nat)
    (rowShape : layout.rowCoordinates=firstRows+secondRows)
    (earlierRounds : List Nat) (queries : Nat)
    (event : LocalChallengePrefix K → LocalChallengePrefix K → K →
      List (GKRBlock K) → List K → List K → List Nat → Prop)
    (scale budget : Nat)
    (joint : ∀ first∈airLocalInitialChallenges sample firstRows,
      ∀ second∈airLocalInitialChallenges sample secondRows,∀ rho∈sample,
      ∀ earlier∈gkrChallengePaths sample earlierRounds,
      count (gkrConcretePCSSamples sample layout queries) (fun item =>
        event (first,item.1.take firstRows) (second,item.1.drop firstRows) rho
          (earlier++[item.2.1]) item.2.2.1 item.2.2.2.1 item.2.2.2.2)*scale≤budget) :
    count ((decodedLocalPrefixes sample firstRows).flatMap (fun p =>
      (decodedLocalPrefixes sample secondRows).flatMap (fun q =>
        (twoTablePCSContinuations sample layout earlierRounds queries).map (fun r => (p,q,r)))))
      (fun x => event x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2)*scale≤
    (airLocalInitialChallenges sample firstRows).length*
      ((airLocalInitialChallenges sample secondRows).length*
        (sample.length*((gkrChallengePaths sample earlierRounds).length*budget))) := by
  classical
  apply two_table_local_joint_budget sample firstRows secondRows
    (twoTablePCSContinuations sample layout earlierRounds queries)
    (fun p q x => event p q x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) scale _
  intro first hf second hs
  rw [←rowShape]
  have each : ∀ rho∈sample,
      count (gkrFullPCSSamples sample layout earlierRounds queries)
        (fun item => event (first,item.1.take firstRows) (second,item.1.drop firstRows) rho
          item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2)*scale≤
        (gkrChallengePaths sample earlierRounds).length*budget := by
    intro rho hr
    exact gkr_full_pcs_event_budget sample layout earlierRounds queries
      (fun rows blocks z path qs => event (first,rows.take firstRows) (second,rows.drop firstRows)
        rho blocks z path qs) scale budget (joint first hf second hs rho hr)
  have summed := sum_scaled_error_budget sample
    (fun rho => count (gkrFullPCSSamples sample layout earlierRounds queries)
      (fun item => event (first,item.1.take firstRows) (second,item.1.drop firstRows) rho
        item.2.1 item.2.2.1 item.2.2.2.1 item.2.2.2.2))
    (fun _ => 0) scale ((gkrChallengePaths sample earlierRounds).length*budget)
    (fun rho hr => by simpa using each rho hr)
  have zero : (sample.map (fun _ => (0:Nat))).sum=0 := by
    clear joint hf hs each summed
    induction sample with
    | nil => rfl
    | cons x xs ih => simpa using ih
  rw [zero,Nat.zero_mul,Nat.add_zero] at summed
  simp only [twoTablePCSContinuations,List.map_flatMap,List.map_map]
  rw [gkr_finite_sample_exchange]
  simpa only [gkrFullPCSSamples,evaluatedGKRExperiment,count,List.countP_flatMap,List.countP_map,
    Function.comp_def] using summed

end NearCompression
