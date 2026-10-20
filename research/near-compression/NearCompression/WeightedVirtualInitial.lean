import NearCompression.UniqueBatchCandidates
import NearCompression.GlobalChainWeightBounds
import NearCompression.GlobalChainTerminalDecomposition

/-! Deterministic initial-candidate reduction for arbitrary (possibly adaptive)
lane coefficients. Existence of a fixed jointly-close polynomial tuple and the
functional discrepancy are explicit; neither follows from a commitment alone. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def weightedLaneValues : List K → List K → K
  | a::as,b::bs => a*b+weightedLaneValues as bs
  | _,_ => 0

def weightedLanePolynomial : List K → List (Poly K) → Poly K
  | a::as,p::ps => Poly.smul a p + weightedLanePolynomial as ps
  | _,_ => Poly.zero

def weightedVirtualOracle (coefficients : List K) (sources : List (K → K)) (x : K) : K :=
  weightedLaneValues coefficients (sources.map (fun source => source x))

theorem weighted_lane_eval (coefficients : List K) (lanes : List (Poly K)) (x : K) :
    (weightedLanePolynomial coefficients lanes).eval x=
      weightedLaneValues coefficients (lanes.map (fun p => p.eval x)) := by
  induction coefficients generalizing lanes with
  | nil => simp [weightedLanePolynomial,weightedLaneValues,Poly.eval_zero]
  | cons a as ih =>
    cases lanes with
    | nil => simp [weightedLanePolynomial,weightedLaneValues,Poly.eval_zero]
    | cons p ps => simp [weightedLanePolynomial,weightedLaneValues,Poly.eval_add,Poly.eval_smul,ih]

theorem weighted_lane_degree (coefficients : List K) (lanes : List (Poly K)) (D : Nat)
    (degrees : ∀ p∈lanes,p.DegLt D) : (weightedLanePolynomial coefficients lanes).DegLt D := by
  induction coefficients generalizing lanes with
  | nil => intro i hi; simp [weightedLanePolynomial,Poly.coeff,Poly.zero]
  | cons a as ih =>
    cases lanes with
    | nil => intro i hi; simp [weightedLanePolynomial,Poly.coeff,Poly.zero]
    | cons p ps =>
      exact Poly.degLt_add (Poly.degLt_smul a (degrees p (by simp)))
        (ih ps (fun q hq => degrees q (by simp [hq])))

theorem weighted_lane_residual (coefficients : List K) (lanes : List (Poly K)) (weights : List K) :
    scalarRSResidual weights (weightedLanePolynomial coefficients lanes)=
      weightedLaneValues coefficients (lanes.map (scalarRSResidual weights)) := by
  have zero : scalarRSResidual weights (Poly.zero : Poly K)=0 := by
    unfold scalarRSResidual
    generalize 0=offset
    induction weights generalizing offset with
    | nil => rfl
    | cons w ws ih =>
      change w*Poly.zero.coeff offset+scalarRSResidualFrom Poly.zero (offset+1) ws=0
      rw [ih]
      simp only [Poly.coeff,Poly.zero,List.getD_nil]; grind
  induction coefficients generalizing lanes with
  | nil => simpa [weightedLanePolynomial,weightedLaneValues] using zero
  | cons a as ih =>
    cases lanes with
    | nil => simpa [weightedLanePolynomial,weightedLaneValues] using zero
    | cons p ps =>
      simp only [weightedLanePolynomial,scalar_rs_residual_add,scalar_rs_residual_scale,
        List.map_cons,weightedLaneValues,ih]

/-- Coefficients may depend on a previous sumcheck point. No randomness or
independent power-batching assumption is needed for this distance statement. -/
theorem weighted_virtual_joint_distance (domain : List K) (coefficients : List K)
    (sources : List (K → K)) (lanes : List (Poly K)) :
    finiteRSMismatches domain (weightedVirtualOracle coefficients sources)
      (weightedLanePolynomial coefficients lanes).eval≤count domain (jointLaneMismatch sources lanes) := by
  apply count_mono
  intro x mismatch equal
  apply mismatch
  rw [weighted_lane_eval]
  exact congrArg (weightedLaneValues coefficients) equal

/-- The scalar candidate can be chosen after all coefficients. A fixed nearby
joint tuple forces that candidate to be its same weighted polynomial batch. -/
theorem weighted_virtual_unique_candidate (domain : List K) (distinct : domain.Nodup)
    (coefficients : List K) (sources : List (K → K)) (lanes : List (Poly K))
    (D R T : Nat) (degrees : ∀ p∈lanes,p.DegLt D)
    (jointClose : count domain (jointLaneMismatch sources lanes)≤R)
    (threshold : T≤domain.length) (separation : R+(domain.length-T)+D≤domain.length)
    (candidate : Poly K) (degree : candidate.DegLt D)
    (agreement : T≤count domain (fun x => weightedVirtualOracle coefficients sources x=candidate.eval x)) :
    ∀ i,candidate.coeff i=(weightedLanePolynomial coefficients lanes).coeff i := by
  have partition := finite_rs_agreement_partition domain (weightedVirtualOracle coefficients sources) candidate.eval
  have close : finiteRSMismatches domain (weightedVirtualOracle coefficients sources) candidate.eval≤domain.length-T := by omega
  have batchClose := Nat.le_trans (weighted_virtual_joint_distance domain coefficients sources lanes) jointClose
  have zero := finite_rs_unique_candidate domain distinct (weightedVirtualOracle coefficients sources)
    candidate (weightedLanePolynomial coefficients lanes) D (domain.length-T) R degree
    (weighted_lane_degree coefficients lanes D degrees) close batchClose (by omega)
  intro i
  have eq := zero i
  rw [Poly.coeff_sub] at eq
  grind

/-- The exact missing input-functional bridge can now supply a scalar
residual discrepancy; candidate proximity cannot conceal it in this basin. -/
theorem weighted_virtual_no_candidate (domain : List K) (distinct : domain.Nodup)
    (coefficients : List K) (sources : List (K → K)) (lanes : List (Poly K))
    (weights : List K) (claim : K) (D R T : Nat)
    (degrees : ∀ p∈lanes,p.DegLt D)
    (jointClose : count domain (jointLaneMismatch sources lanes)≤R)
    (threshold : T≤domain.length) (separation : R+(domain.length-T)+D≤domain.length)
    (wrong : weightedLaneValues coefficients (lanes.map (scalarRSResidual weights))≠claim) :
    ¬∃ candidate : Poly K,candidate.DegLt D ∧ scalarRSResidual weights candidate=claim ∧
      T≤count domain (fun x => weightedVirtualOracle coefficients sources x=candidate.eval x) := by
  rintro ⟨candidate,degree,residual,agreement⟩
  have equal := weighted_virtual_unique_candidate domain distinct coefficients sources lanes D R T
    degrees jointClose threshold separation candidate degree agreement
  have same := scalar_rs_residual_congr candidate (weightedLanePolynomial coefficients lanes) weights equal
  rw [weighted_lane_residual,residual] at same
  exact wrong same.symm

private theorem unit_cap_mass (domain : List Nat) (weight : Nat → Nat) (event : Nat → Prop)
    (cap : ∀ x∈domain,weight x≤1) : consistencyMass domain weight event≤count domain event := by
  classical
  induction domain with
  | nil => simp [consistencyMass,count]
  | cons x xs ih =>
    have head := cap x (by simp)
    have tail := ih (fun y hy => cap y (by simp [hy]))
    simp only [consistencyMass,count,List.map_cons,List.sum_cons,List.countP_cons] at tail ⊢
    by_cases h : event x <;> simp_all <;> omega

/-- Directly discharges the initial predicate used by the interactive folding
soundness theorem. The source oracle is the actual weighted virtual word.
The lift to a common RS domain and joint proximity are caller obligations. -/
theorem weighted_virtual_no_initial {K : Type} [Field K]
    (N0 : Nat) (sizes degrees : Nat → Nat) (roots challenges : Nat → K)
    (oracles : Nat → Nat → K) (allWeights : Nat → List K) (claims : Nat → K)
    (coefficients : List K) (sources : List (K → K)) (lanes : List (Poly K)) (R T : Nat)
    (sizeInitial : sizes 0=N0)
    (domainDistinct : ((List.range N0).map (fun i => roots 0^i)).Nodup)
    (source : ∀ i<N0,oracles 0 i=weightedVirtualOracle coefficients sources (roots 0^i))
    (laneDegrees : ∀ p∈lanes,p.DegLt (degrees 0))
    (jointClose : count ((List.range N0).map (fun i => roots 0^i)) (jointLaneMismatch sources lanes)≤R)
    (threshold : T≤N0) (separation : R+(N0-T)+degrees 0≤N0)
    (wrong : weightedLaneValues coefficients (lanes.map (scalarRSResidual (allWeights 0)))≠claims 0) :
    ¬indexedChainCandidate N0 sizes degrees roots challenges oracles allWeights claims T 0 := by
  rintro ⟨candidate,degree,residual,mass⟩
  have cap : ∀ y∈List.range N0,
      globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes roots challenges oracles) 0 y≤1 := by
    intro y hy
    simpa using global_chain_weight_cap N0 sizes (globalRSChainCheck sizes roots challenges oracles)
      0 sizeInitial (by intro j hj; omega) y (by rw [sizeInitial]; exact List.mem_range.mp hy)
  rw [sizeInitial] at mass
  have agreement := Nat.le_trans mass (unit_cap_mass _ _ _ cap)
  have transfer : count (List.range N0) (fun y => oracles 0 y=candidate.eval (roots 0^y))=
      count ((List.range N0).map (fun i => roots 0^i))
        (fun x => weightedVirtualOracle coefficients sources x=candidate.eval x) := by
    classical
    simp only [count,List.countP_map,Function.comp_def]
    apply List.countP_congr
    intro i hi
    constructor
    · intro h
      have eq := @_root_.of_decide_eq_true _ (Classical.propDecidable _) h
      have result : weightedVirtualOracle coefficients sources (roots 0^i)=candidate.eval (roots 0^i) :=
        (source i (List.mem_range.mp hi)).symm.trans eq
      exact @_root_.decide_eq_true _ (Classical.propDecidable _) result
    · intro h
      have eq := @_root_.of_decide_eq_true _ (Classical.propDecidable _) h
      have result : oracles 0 i=candidate.eval (roots 0^i) := (source i (List.mem_range.mp hi)).trans eq
      exact @_root_.decide_eq_true _ (Classical.propDecidable _) result
  rw [transfer] at agreement
  apply weighted_virtual_no_candidate ((List.range N0).map (fun i => roots 0^i)) domainDistinct
    coefficients sources lanes (allWeights 0) (claims 0) (degrees 0) R T laneDegrees jointClose
    (by simpa using threshold) (by simpa using separation) wrong
  exact ⟨candidate,degree,residual,agreement⟩

end NearCompression
