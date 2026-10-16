import NearCompression.RecoveredHeterogeneousClaim
import NearCompression.GenericPackedOpeningComposition
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- The near-case lifted weight MLE and the far-case joint beta use the
same PCS coordinates, including skipped low coordinates of smaller lanes. -/
theorem heterogeneous_lifted_joint_coefficients (layout : GKRJointLayout)
    (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout) (point : Nat → K) :
    functionalBatchCoefficients layout.commonLog
      (liftedHeterogeneousWeights layout.commonLog layout.inputLog metadata
        (fun lane => gkrPointBlock lane.rowOffset lane.rowLog point)
        (gkrPointBlock layout.rowCoordinates layout.inputLog point)
        (gkrPointBlock (layout.rowCoordinates+layout.inputLog) layout.inputLog point)
        (point (layout.rowCoordinates+2*layout.inputLog)))
      (fun i => point (layout.rowCoordinates+2*layout.inputLog+1+i))=
      metadata.map (fun lane => heterogeneousJointBeta layout lane point) := by
  unfold functionalBatchCoefficients liftedHeterogeneousWeights
  rw [List.map_map]
  apply List.map_congr_left
  intro lane member
  have fits := (valid lane member).2.1
  have dimension : layout.commonLog-(lane.rowLog+lane.packingLog)+
      (lane.rowLog+lane.packingLog)=layout.commonLog := by omega
  have repeated := repeated_low_weight_mle (layout.commonLog-(lane.rowLog+lane.packingLog))
    (lane.rowLog+lane.packingLog)
    (heterogeneousLaneWeight layout.inputLog lane
      (gkrPointBlock lane.rowOffset lane.rowLog point)
      (gkrPointBlock layout.rowCoordinates layout.inputLog point)
      (gkrPointBlock (layout.rowCoordinates+layout.inputLog) layout.inputLog point)
      (point (layout.rowCoordinates+2*layout.inputLog)))
    (fun i => point (layout.rowCoordinates+2*layout.inputLog+1+i))
  rw [dimension] at repeated
  change genericRowMLE _ _ _=heterogeneousJointBeta layout lane point
  rw [repeated]
  unfold heterogeneousJointBeta heterogeneousLaneBeta
  apply packed_row_mle_point_congr
  intro i hi
  simp only [gkrPointBlock,hi,ite_true]
  congr 1
  omega

/-- Exact identity of the initial virtual source in the near and far
formulations. Received source words may be arbitrary; no polynomial honesty,
proximity, commitment binding or randomness premise is used. -/
theorem heterogeneous_lifted_joint_oracle (layout : GKRJointLayout)
    (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (sources : List (K → K)) (point : List K) (x : K) :
    weightedVirtualOracle
      (functionalBatchCoefficients layout.commonLog
        (liftedHeterogeneousWeights layout.commonLog layout.inputLog metadata
          (fun lane => gkrPointBlock lane.rowOffset lane.rowLog (fun i => point.getD i 0))
          (gkrPointBlock layout.rowCoordinates layout.inputLog (fun i => point.getD i 0))
          (gkrPointBlock (layout.rowCoordinates+layout.inputLog) layout.inputLog (fun i => point.getD i 0))
          (point.getD (layout.rowCoordinates+2*layout.inputLog) 0))
        (fun i => point.getD (layout.rowCoordinates+2*layout.inputLog+1+i) 0)) sources x=
      jointBetaSource (metadata.map (heterogeneousJointBeta layout)) sources x point := by
  rw [heterogeneous_lifted_joint_coefficients layout metadata valid]
  simp only [jointBetaSource,List.map_map,Function.comp_def]

end NearCompression
