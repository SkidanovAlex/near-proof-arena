import NearCompression.JointSourceBaseDescent
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

/-- Trailing zeros and other polynomial list representations cannot change
recovered columns when all coefficients agree. -/
theorem recovered_column_coefficient_congr {K : Type} [Field K]
    (C : Nat) (lane : GKRSourceLane) (offset : Nat) (left right : Poly K)
    (same : ∀ i,left.coeff i=right.coeff i) :
    recoveredColumnValues C lane offset left=recoveredColumnValues C lane offset right := by
  have projected : ∀ L d,recoverProjectedPolynomial L d left=recoverProjectedPolynomial L d right := by
    intro L d
    unfold recoverProjectedPolynomial
    congr 1
    apply List.map_congr_left
    intro i _
    exact same (L*i)
  unfold recoveredColumnValues
  rw [projected]

/-- Two joint tuples may have different auxiliary oracles. If their selected
source oracle is identical, unique-decoding separation fixes that source
lane's recovered columns across both tuples. -/
theorem joint_shared_source_recovered_equal {K : Type} [Field K]
    (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout) (geometry : CanonicalLaneSelectors layout metadata)
    (domain : List K) (distinct : domain.Nodup) (D T : Nat)
    (leftSources rightSources : List (K → K)) (left right : List (Poly K))
    (leftShape : leftSources.length=metadata.length) (rightShape : rightSources.length=metadata.length)
    (leftRep : JointBetaRepresentative domain (fun _=>1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) leftSources left)
    (rightRep : JointBetaRepresentative domain (fun _=>1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) rightSources right)
    (separation : 2*(domain.length-T)+D≤domain.length)
    (i : Nat) (hi : i<metadata.length)
    (sameSource : leftSources[i]=rightSources[i]) (offset : Nat) :
    recoveredColumnValues layout.commonLog metadata[i] offset (left[i]'(by have h:=leftRep.1;omega))=
      recoveredColumnValues layout.commonLog metadata[i] offset (right[i]'(by have h:=rightRep.1;omega)) := by
  have ls : left.length=metadata.length := leftRep.1.trans leftShape
  have rs : right.length=metadata.length := rightRep.1.trans rightShape
  have lc := joint_representative_lane_radius layout metadata valid geometry domain D T leftSources left leftShape ls leftRep i hi
  have rc := joint_representative_lane_radius layout metadata valid geometry domain D T rightSources right rightShape rs rightRep i hi
  rw [←sameSource] at rc
  have zero := finite_rs_unique_candidate domain distinct leftSources[i] left[i] right[i] D
    (domain.length-T) (domain.length-T) (leftRep.2.1 _ (List.getElem_mem _))
    (rightRep.2.1 _ (List.getElem_mem _)) lc rc (by omega)
  apply recovered_column_coefficient_congr
  intro j
  have h := zero j
  rw [Poly.coeff_sub] at h
  grind

/-- A single recovered source lane can be selected before any later auxiliary
choice. There need not be a valid representative for every choice; when none
exists the conclusion is vacuous. This is an ideal-model choice, not an
algorithm extracting polynomial preimages from a commitment. -/
theorem fixed_source_column_before_auxiliary {K A : Type} [Field K]
    (domain : List K) (distinct : domain.Nodup) (source : K → K) (D radius : Nat)
    (separation : radius+radius+D≤domain.length)
    (C : Nat) (lane : GKRSourceLane) (candidates : A → Poly K) (eligible : A → Prop)
    (degree : ∀ a,eligible a → (candidates a).DegLt D)
    (close : ∀ a,eligible a → finiteRSMismatches domain source (candidates a).eval≤radius) :
    ∃ decoded : Nat → Nat → K,∀ a,eligible a → ∀ offset,
      recoveredColumnValues C lane offset (candidates a)=decoded offset := by
  classical
  by_cases any : ∃ a,eligible a
  · obtain ⟨anchor,ha⟩ := any
    refine ⟨fun offset => recoveredColumnValues C lane offset (candidates anchor),?_⟩
    intro a he offset
    have zero := finite_rs_unique_candidate domain distinct source (candidates a) (candidates anchor) D radius radius
      (degree a he) (degree anchor ha) (close a he) (close anchor ha) separation
    apply recovered_column_coefficient_congr
    intro j
    have h := zero j
    rw [Poly.coeff_sub] at h
    grind
  · exact ⟨fun _ _ => 0,fun a ha => False.elim (any ⟨a,ha⟩)⟩

end NearCompression
