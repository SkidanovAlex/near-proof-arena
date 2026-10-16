import NearCompression.GKRProjectedRepresentative
import NearCompression.RecoveredGKRTable
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Two universal representatives of the same fixed received oracles have
identical lane coefficients under the explicit unique-decoding separation.
The received oracles need not be polynomial, honest, or fully disclosed. -/
theorem joint_source_representative_unique (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (domain : List K) (distinct : domain.Nodup) (D T : Nat) (sources : List (K→K))
    (sourceShape : sources.length=metadata.length) (left right : List (Poly K))
    (leftRep : JointBetaRepresentative domain (fun _=>1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) sources left)
    (rightRep : JointBetaRepresentative domain (fun _=>1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) sources right)
    (separation : 2*(domain.length-T)+D≤domain.length)
    (i : Nat) (hi : i<metadata.length) :
    ∀ j,(left[i]'(by have h:=leftRep.1;omega)).coeff j=(right[i]'(by have h:=rightRep.1;omega)).coeff j := by
  have ls : left.length=metadata.length := leftRep.1.trans sourceShape
  have rs : right.length=metadata.length := rightRep.1.trans sourceShape
  have lc := joint_representative_lane_radius layout metadata valid geometry domain D T sources left
    sourceShape ls leftRep i hi
  have rc := joint_representative_lane_radius layout metadata valid geometry domain D T sources right
    sourceShape rs rightRep i hi
  have zero := finite_rs_unique_candidate domain distinct sources[i]
    left[i] right[i] D (domain.length-T) (domain.length-T)
    (leftRep.2.1 _ (List.getElem_mem _)) (rightRep.2.1 _ (List.getElem_mem _)) lc rc (by omega)
  intro j
  have equal:=zero j
  rw [Poly.coeff_sub] at equal
  grind

/-- Fixed-length coefficient storage avoids ambiguity from trailing zeros. -/
def jointSourceCoefficientNormalForm (D : Nat) (polys : List (Poly K)) : List (List K) :=
  polys.map (fun p=>(List.range D).map p.coeff)

theorem joint_source_normal_form_unique (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (domain : List K) (distinct : domain.Nodup) (D T : Nat) (sources : List (K→K))
    (sourceShape : sources.length=metadata.length) (left right : List (Poly K))
    (leftRep : JointBetaRepresentative domain (fun _=>1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) sources left)
    (rightRep : JointBetaRepresentative domain (fun _=>1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) sources right)
    (separation : 2*(domain.length-T)+D≤domain.length) :
    jointSourceCoefficientNormalForm D left=jointSourceCoefficientNormalForm D right := by
  have ls : left.length=metadata.length := leftRep.1.trans sourceShape
  have rs : right.length=metadata.length := rightRep.1.trans sourceShape
  apply List.ext_getElem (by simp [jointSourceCoefficientNormalForm,ls,rs])
  intro i hl hr
  have hi : i<metadata.length := by simpa [jointSourceCoefficientNormalForm,ls] using hl
  simp only [jointSourceCoefficientNormalForm,List.getElem_map]
  apply List.map_congr_left
  intro j hj
  exact joint_source_representative_unique layout metadata valid geometry domain distinct D T sources sourceShape
    left right leftRep rightRep separation i hi j

/-- Equality of coefficients forces equality of the entire decoded row/column
assignment, before any rowpoint, GKR point or opening weights are selected. -/
theorem recovered_table_of_coefficient_identity (left right : Poly K)
    (same : ∀ j,left.coeff j=right.coeff j) (L d n p : Nat) :
    recoveredGKRTable n p (recoverProjectedPolynomial L d left)=
      recoveredGKRTable n p (recoverProjectedPolynomial L d right) := by
  have recovered : recoverProjectedPolynomial L d left=recoverProjectedPolynomial L d right := by
    unfold recoverProjectedPolynomial
    congr 1
    apply List.map_congr_left
    intro j hj
    exact same (L*j)
  rw [recovered]

/-- Mathematical selection depends only on the fixed domain, source oracles,
metadata and thresholds. It has no rowpoint/GKR/PCS-challenge argument.
Existence is NOT inferred from a Merkle root or sampled protocol acceptance. -/
noncomputable def chosenJointSourceRepresentative (layout : GKRJointLayout)
    (metadata : List GKRSourceLane) (domain : List K) (D T : Nat) (sources : List (K→K)) : List (Poly K) := by
  classical
  exact if h : ∃ polys,JointBetaRepresentative domain (fun _=>1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) sources polys then Classical.choose h else []

theorem chosen_joint_source_representative_valid (layout : GKRJointLayout)
    (metadata : List GKRSourceLane) (domain : List K) (D T : Nat) (sources : List (K→K))
    (existsRep : ∃ polys,JointBetaRepresentative domain (fun _=>1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) sources polys) :
    JointBetaRepresentative domain (fun _=>1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) sources
      (chosenJointSourceRepresentative layout metadata domain D T sources) := by
  classical
  simp only [chosenJointSourceRepresentative,dite_eq_left existsRep]
  exact Classical.choose_spec existsRep
end NearCompression
