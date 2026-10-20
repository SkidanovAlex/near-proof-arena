import NearCompression.CheckedHistoryAcceptance
import NearCompression.WeightedVirtualInitial
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Near-source counterpart to checked_history_joint_far_acceptance_budget.
A wrong functional of a fixed jointly-close tuple forces initial candidate
absence. Coefficients can depend on earlier challenges; all later fold states
remain adaptive subject to the explicit prechallenge bindings. This theorem
does not obtain the close tuple from a Merkle root. -/
theorem checked_history_joint_near_acceptance_budget
    (sample : List K) (distinct : sample.Nodup)
    (strategy : List K→GeneralFoldTranscript K) (N0 T rounds q : Nat)
    (sizes degrees : Nat→Nat) (initial : sizes 0=N0)
    (positive : ∀ j≤rounds,0<sizes j)
    (sizeHalves : ∀ j<rounds,sizes j=2*sizes (j+1))
    (degreeHalves : ∀ j<rounds,degrees j=2*degrees (j+1))
    (regime : 2*N0+degrees 0<3*T) (h2 : (2:K)≠0)
    (fixed : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).snapshot N0 sizes h.length=(strategy h).snapshot N0 sizes h.length)
    (weights : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).weights h.length=(strategy h).weights h.length)
    (claim : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).claims h.length=(strategy h).claims h.length)
    (challenge : ∀ h : List K,h.length<rounds → ∀ r∈sample,
      (strategy (h++[r])).challenges h.length=r)
    (coefficients : List K) (sources : List (K→K)) (lanes : List (Poly K)) (R : Nat)
    (domainDistinct : ((List.range N0).map (fun i=>(strategy []).roots 0^i)).Nodup)
    (sourceValues : ∀ i<N0,(strategy []).oracles 0 i=
      weightedVirtualOracle coefficients sources ((strategy []).roots 0^i))
    (laneDegrees : ∀ p∈lanes,p.DegLt (degrees 0))
    (jointClose : count ((List.range N0).map (fun i=>(strategy []).roots 0^i))
      (jointLaneMismatch sources lanes)≤R)
    (threshold : T≤N0) (separation : R+(N0-T)+degrees 0≤N0)
    (wrong : weightedLaneValues coefficients (lanes.map (scalarRSResidual ((strategy []).weights 0)))≠
      (strategy []).claims 0) :
    count ((uniformTuples sample rounds).flatMap (fun path=>
      (uniformTuples (List.range N0) q).map (fun queries=>(path,queries))))
      (fun pair=>checkedHistoryAccept strategy sizes degrees pair.1 pair.2)*sample.length≤
      ((List.range rounds).map (fun i=>max (sizes (i+1)) 2)).sum*sample.length^rounds*N0^q+sample.length^(rounds+1)*(T-1)^q := by
  have absent:=weighted_virtual_no_initial N0 sizes degrees (strategy []).roots (strategy []).challenges
    (strategy []).oracles (strategy []).weights (strategy []).claims coefficients sources lanes R T
    initial domainDistinct sourceValues laneDegrees jointClose threshold separation wrong
  exact checked_history_interactive_acceptance_budget sample distinct strategy N0 T rounds q sizes degrees
    initial positive sizeHalves degreeHalves regime h2 fixed weights claim challenge absent
end NearCompression
