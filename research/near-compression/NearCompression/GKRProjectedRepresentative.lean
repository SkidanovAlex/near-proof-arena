import NearCompression.GKRJointLaneSeparation
import NearCompression.ProjectedSourceRecovery
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

private theorem unit_mass_count (domain : List K) (event : K → Prop) :
    consistencyMass domain (fun _ => 1) event=count domain event := by
  classical
  induction domain with
  | nil => simp [consistencyMass,count]
  | cons x xs ih =>
    simp only [consistencyMass,count,List.map_cons,List.sum_cons,List.countP_cons] at ih ⊢
    by_cases h : event x <;> simp_all <;> omega

/-- A single fixed universal representative gives each selected lane an
ordinary RS proximity bound. The unit-weight initial domain is explicit. -/
theorem joint_representative_lane_radius (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (domain : List K) (D T : Nat) (sources : List (K → K)) (polys : List (Poly K))
    (sourceShape : sources.length=metadata.length) (polyShape : polys.length=metadata.length)
    (representative : JointBetaRepresentative domain (fun _ => 1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) sources polys)
    (i : Nat) (hi : i<metadata.length) :
    finiteRSMismatches domain sources[i] polys[i].eval≤domain.length-T := by
  have mass := joint_representative_lane_mass layout metadata valid geometry domain (fun _ => 1)
    D T sources polys sourceShape representative
  have single : T≤consistencyMass domain (fun _ => 1) (fun x => sources[i] x=polys[i].eval x) := by
    apply Nat.le_trans mass
    apply consistency_mass_mono
    intro x hx agree
    have eq := agree i hi
    have si : i<sources.length := by omega
    have pi : i<polys.length := by omega
    simpa [List.getD,si,pi] using eq
  rw [unit_mass_count] at single
  have partition := finite_rs_agreement_partition domain sources[i] polys[i].eval
  omega

/-- Recover the selected original-branch polynomial from the SAME fixed
universal tuple. No honest-source or sparse-image premise is assumed.
The finite RS domain/root-order certificates remain explicit. -/
theorem joint_representative_projected_recovery (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (domain : List K) (distinct : domain.Nodup) (D T : Nat)
    (sources : List (K → K)) (polys : List (Poly K))
    (sourceShape : sources.length=metadata.length) (polyShape : polys.length=metadata.length)
    (representative : JointBetaRepresentative domain (fun _ => 1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) sources polys)
    (i : Nat) (hi : i<metadata.length)
    (L d : Nat) (positive : 0<L) (degrees : D=L*d)
    (source : K → K) (projection : ∀ x,sources[i] x=source (x^L))
    (z : K) (period : z^L=1) (order : ∀ j,¬L∣j → z^j≠1)
    (closed : (domain.map (fun x => z*x)).Perm domain)
    (separation : (domain.length-T)+(domain.length-T)+D≤domain.length) :
    let recovered := recoverProjectedPolynomial L d polys[i]
    recovered.DegLt d ∧
      (∀ j,polys[i].coeff j=if L∣j then recovered.coeff (j/L) else 0) := by
  have degree : polys[i].DegLt D := representative.2.1 _ (List.getElem_mem _)
  have close := joint_representative_lane_radius layout metadata valid geometry domain D T sources polys
    sourceShape polyShape representative i hi
  have symmetric (x : K) : sources[i] (z*x)=sources[i] x := by
    rw [projection,projection]
    exact power_projected_source_symmetry source z L period x
  have sparse := projected_source_sparse_coefficients domain distinct z L order closed sources[i]
    symmetric polys[i] D (domain.length-T) degree close separation
  exact ⟨recovered_projected_degree _ _ _,fun j => recovered_projected_coefficients L d positive polys[i]
    (by simpa only [degrees] using degree) sparse j⟩
end NearCompression
