import NearCompression.HeterogeneousGKRWeights
import NearCompression.JointSourceFarFold

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Ideal checked-fold FAR bound for the explicit heterogeneous source family.
No arbitrary beta-affinity premise remains. Metadata correctness, causal
upstream sampling, near-case image recovery and cryptographic binding remain
separate obligations; raw strategy causality is still explicit. -/
theorem heterogeneous_far_checked_count (sample : List K) (sampleDistinct : sample.Nodup)
    (omega : K) (N D T rounds queries : Nat) (sizes degrees : Nat → Nat)
    (domainDistinct : ((List.range N).map (fun i => omega^i)).Nodup)
    (sizeInitial : sizes 0=N) (degreeInitial : degrees 0=D)
    (positive : ∀ i≤rounds,0<sizes i)
    (sizeHalves : ∀ i<rounds,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<rounds,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (regime : 2*N+D<3*T) (threshold : D-1<T)
    (layout : GKRJointLayout) (entries : List (GKRSourceLane × (K → K)))
    (valid : ∀ entry∈entries,entry.1.WellFormed layout)
    (far : ¬∃ lanes,JointBetaRepresentative ((List.range N).map (fun i => omega^i))
      (fun _ => 1) (heterogeneousJointDimension layout) D T (heterogeneousBetas layout entries) (heterogeneousSources layout entries) lanes)
    (raw : List K → List K → FoldTranscript K)
    (causal : ∀ point∈uniformTuples sample (heterogeneousJointDimension layout),∀ path∈uniformTuples sample rounds,∀ i<rounds,
      (jointSourceStrategy omega (heterogeneousBetas layout entries) (heterogeneousSources layout entries) raw point path).snapshot N sizes i=
      (jointSourceStrategy omega (heterogeneousBetas layout entries) (heterogeneousSources layout entries) raw point (path.take i)).snapshot N sizes i)
    (challengeValues : ∀ point∈uniformTuples sample (heterogeneousJointDimension layout),∀ path∈uniformTuples sample rounds,∀ i<rounds,
      (jointSourceStrategy omega (heterogeneousBetas layout entries) (heterogeneousSources layout entries) raw point path).challenges i=path[i]?.getD 0) :
    count ((uniformTuples sample (heterogeneousJointDimension layout)).flatMap (fun point =>
      (functionalFoldSamples sample N rounds queries).map (fun pair => (point,pair))))
      (fun pair => checkedFoldAccept (jointSourceStrategy omega (heterogeneousBetas layout entries) (heterogeneousSources layout entries) raw pair.1)
        N sizes degrees T rounds pair.2.1 pair.2.2)*sample.length ≤
      (heterogeneousJointDimension layout)*max N 2*sample.length^((heterogeneousJointDimension layout)-1)*(sample.length^rounds*N^queries)*sample.length+
      sample.length^(heterogeneousJointDimension layout)*(((List.range rounds).map (fun i => max (sizes (i+1)) 2)).sum*
        sample.length^rounds*N^queries+sample.length^(rounds+1)*(T-1)^queries) := by
  exact joint_source_far_checked_count sample sampleDistinct omega
    (heterogeneousJointDimension layout) N D T rounds queries sizes degrees
    domainDistinct sizeInitial degreeInitial positive sizeHalves degreeHalves
    h2 regime threshold (heterogeneousBetas layout entries)
    (heterogeneousSources layout entries) (heterogeneous_betas_affine layout entries valid)
    far raw causal challengeValues

end NearCompression
