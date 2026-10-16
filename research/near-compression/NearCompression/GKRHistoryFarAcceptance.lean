import NearCompression.GKRHistoryCoordinates
import NearCompression.JointSourceAcceptance
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Far-case checked folding acceptance for the actual heterogeneous joint
family and fixed-length PCS suffix extraction. On valid joint vectors this
is the same take/drop suffix used by the near experiment. Initial claims and
folding strategies may depend on the full vector. This remains ideal-oracle
soundness, with source identities and terminal authentication explicit. -/
theorem gkr_history_far_acceptance_count [DecidableEq K]
    (sample : List K) (sampleDistinct : sample.Nodup)
    (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (N T queries : Nat) (sizes degrees : Nat → Nat) (roots : Nat → K)
    (sources : List (K → K))
    (far : ¬∃ lanes,JointBetaRepresentative ((List.range N).map (fun i => roots 0^i))
      (fun _ => 1) (heterogeneousJointDimension layout) (degrees 0) T (metadata.map (heterogeneousJointBeta layout)) sources lanes)
    (initial : List K → K) (provers : List K → WeightedPrefixProver K)
    (sourceValues : ∀ z,∀ i<N,(provers z).oracle 0 [] i=
      jointBetaSource (metadata.map (heterogeneousJointBeta layout)) sources (roots 0^i) z)
    (domainDistinct : ((List.range N).map (fun i => roots 0^i)).Nodup)
    (interpolation : degrees 0-1<T)
    (sizeInitial : sizes 0=N) (positive : ∀ i≤layout.commonLog,0<sizes i)
    (sizeHalves : ∀ i<layout.commonLog,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<layout.commonLog,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (regime : 2*N+degrees 0<3*T)
    (pointInjective : ∀ i<layout.commonLog,∀ a<sizes (i+1),∀ b<sizes (i+1),roots (i+1)^a=roots (i+1)^b → a=b)
    (nonzero : ∀ i<layout.commonLog,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<layout.commonLog,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<layout.commonLog,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (terminalDegree : 1≤degrees layout.commonLog)
    (terminalAuthenticated : ∀ z,∀ path∈uniformTuples sample layout.commonLog,
      weightedReplayCheck (gkrPCSPoint layout z) path ((provers z).messages layout.commonLog path)
        (initial z) ((provers z).terminal path)=true →
      ∀ y<sizes layout.commonLog,(provers z).oracles path layout.commonLog y=(provers z).terminal path) :
    let outer := uniformTuples sample (heterogeneousJointDimension layout)
    let inner := (uniformTuples sample layout.commonLog).flatMap (fun path =>
      (uniformTuples (List.range N) queries).map (fun qs => (path,qs)))
    count (outer.flatMap (fun z => inner.map (fun pair => (z,pair))))
      (fun pair => weightedReplayAccept (gkrPCSPoint layout pair.1) (initial pair.1)
        ((provers pair.1).messages layout.commonLog) (provers pair.1).terminal roots
        (provers pair.1).oracles sizes pair.2.1 pair.2.2)*sample.length≤
      ((heterogeneousJointDimension layout)*max N 2*sample.length^((heterogeneousJointDimension layout)-1))*inner.length*sample.length+
      outer.length*(((List.range layout.commonLog).map (fun i => max (sizes (i+1)) 2)).sum*
        sample.length^layout.commonLog*N^queries+sample.length^(layout.commonLog+1)*(T-1)^queries) := by
  apply joint_source_far_acceptance_count sample sampleDistinct
    (heterogeneousJointDimension layout) layout.commonLog N T queries sizes degrees roots
    (metadata.map (heterogeneousJointBeta layout)) sources _ far
    (gkrPCSPoint layout) (gkr_pcs_point_length layout) initial provers sourceValues
    domainDistinct interpolation sizeInitial positive sizeHalves degreeHalves h2 regime
    pointInjective nonzero squared negative terminalDegree terminalAuthenticated
  intro beta member point coordinate bound r
  obtain ⟨lane,hl,rfl⟩ := List.mem_map.mp member
  exact heterogeneous_joint_beta_affine layout lane (valid lane hl) point coordinate bound r

end NearCompression
