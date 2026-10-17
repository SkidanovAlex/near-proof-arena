import NearCompression.GKRProjectedRepresentative
import NearCompression.CloseFamilySumcheck
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

omit [Field K] in
private theorem unit_mass_count (domain : List K) (event : K → Prop) :
    consistencyMass domain (fun _ => 1) event=count domain event := by
  classical
  induction domain with
  | nil => simp [consistencyMass,count]
  | cons x xs ih =>
    simp only [consistencyMass,count,List.map_cons,List.sum_cons,List.countP_cons] at ih ⊢
    by_cases h : event x <;> simp_all <;> omega

/-- A fixed universal representative supplies a simultaneous proximity
representative for ANY weight-table family, without choosing new polynomials
when an obligation/rowpoint/GKR point changes. -/
theorem joint_representative_shared_functional {Obligation : Type}
    (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (domain : List K) (D T n : Nat) (sources : List (K → K)) (polys : List (Poly K))
    (sourceShape : sources.length=metadata.length)
    (representative : JointBetaRepresentative domain (fun _ => 1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) sources polys)
    (tables : Obligation → List (Nat → K))
    (tableShape : ∀ obligation,(tables obligation).length=metadata.length) :
    SharedFunctionalRepresentative domain n D (domain.length-T) tables sources polys := by
  have polyShape : polys.length=metadata.length := representative.1.trans sourceShape
  refine ⟨representative.2.1,representative.1.symm,?_,?_⟩
  · intro obligation
    rw [tableShape,polyShape]
  · intro obligation point
    have joint := joint_representative_lane_mass layout metadata valid geometry domain (fun _ => 1)
      D T sources polys sourceShape representative
    have single : T≤consistencyMass domain (fun _ => 1) (fun x =>
        weightedVirtualOracle (functionalBatchCoefficients n (tables obligation) point) sources x=
        (weightedLanePolynomial (functionalBatchCoefficients n (tables obligation) point) polys).eval x) := by
      apply Nat.le_trans joint
      apply consistency_mass_mono
      intro x hx agree
      have same : sources.map (fun f => f x)=polys.map (fun p => p.eval x) := by
        apply List.ext_getElem (by simp [sourceShape,polyShape])
        intro i h1 h2
        have hi : i<metadata.length := by simpa only [List.length_map,sourceShape] using h1
        have eq := agree i hi
        have hs : i<sources.length := by omega
        have hp : i<polys.length := by omega
        simpa [List.getD,hs,hp] using eq
      rw [weighted_lane_eval]
      unfold weightedVirtualOracle
      rw [same]
    rw [unit_mass_count] at single
    have partition := finite_rs_agreement_partition domain
      (weightedVirtualOracle (functionalBatchCoefficients n (tables obligation) point) sources)
      (weightedLanePolynomial (functionalBatchCoefficients n (tables obligation) point) polys).eval
    omega

/-- Actual checked quadratic weighted-sumcheck near-case bound, deriving its
close-family premise from universal heterogeneous-source agreement and
natural slot geometry. The witness tuple is fixed before the weighted
sumcheck; earlier challenges may select the displayed fixed tables/strategy. -/
theorem joint_representative_near_sumcheck_count (layout : GKRJointLayout)
    (metadata : List GKRSourceLane) (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (domain sample : List K) (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (D T n : Nat) (sources : List (K → K)) (polys : List (Poly K))
    (sourceShape : sources.length=metadata.length)
    (representative : JointBetaRepresentative domain (fun _ => 1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) sources polys)
    (tables : List (Nat → K)) (tableShape : tables.length=metadata.length)
    (threshold : T≤domain.length) (separation : 2*(domain.length-T)+D≤domain.length)
    (sent : List K → Poly K) (claim : List K → K)
    (wrong : claim []≠coefficientTableFunctional n tables polys) :
    count (uniformTuples sample n) (fun path => weightedSumcheckChecks sent claim [] path ∧
      ∃ candidate : Poly K,candidate.DegLt D ∧
        scalarRSResidual (equalityWeights path) candidate=claim path ∧
        T≤count domain (fun x => weightedVirtualOracle
          (functionalBatchCoefficients n tables (fun i => path.getD i 0)) sources x=candidate.eval x)) *sample.length≤
      (2*n)*sample.length^n := by
  exact close_family_sumcheck_residual_count domain sample domainDistinct sampleDistinct n D T tables sources polys
    (joint_representative_shared_functional layout metadata valid geometry domain D T n sources polys sourceShape
      representative (fun _ : Unit => tables) (fun _ => tableShape)) threshold separation sent claim wrong
end NearCompression
