import NearCompression.WeightedVirtualInitial
import NearCompression.GenericPackedClaimAuthentication

/-! Functional quotient and scalar-basin initial reduction. Tables here live
on the COMMON lifted coefficient cube. Their correspondence with sparse lifts,
current/next input slots and GKR weights must be established by the caller.
A representative is ONE fixed ordered polynomial tuple across all obligations
and all later points, never a separately chosen witness for each functional. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- The actual structured coefficient family: each lane weight is an MLE. -/
def functionalBatchCoefficients (n : Nat) (tables : List (Nat → K))
    (point : Nat → K) : List K := tables.map (fun w => genericRowMLE n w point)

/-- Requested functional of the common-domain polynomial coefficient tuple. -/
def coefficientTableFunctional (n : Nat) (tables : List (Nat → K)) (lanes : List (Poly K)) : K :=
  ((List.range (2^n)).map (fun i => weightedLaneValues (tables.map (fun w => w i))
    (lanes.map (fun p => p.coeff i)))).sum

def FunctionalBatchEquivalent (n : Nat) (tables : List (Nat → K))
    (left right : List (Poly K)) : Prop :=
  ∀ point i,(weightedLanePolynomial (functionalBatchCoefficients n tables point) left).coeff i=
    (weightedLanePolynomial (functionalBatchCoefficients n tables point) right).coeff i

theorem weighted_lane_coefficient (coefficients : List K) (lanes : List (Poly K)) (i : Nat) :
    (weightedLanePolynomial coefficients lanes).coeff i=
      weightedLaneValues coefficients (lanes.map (fun p => p.coeff i)) := by
  induction coefficients generalizing lanes with
  | nil => simp [weightedLanePolynomial,weightedLaneValues,Poly.coeff,Poly.zero]
  | cons a as ih =>
    cases lanes with
    | nil => simp [weightedLanePolynomial,weightedLaneValues,Poly.coeff,Poly.zero]
    | cons p ps =>
      simp only [weightedLanePolynomial,Poly.coeff_add,Poly.coeff_smul,List.map_cons,weightedLaneValues,ih]

theorem functional_batch_boolean (n : Nat) (tables : List (Nat → K)) (bits : Nat → Bool) :
    functionalBatchCoefficients n tables (genericRowBooleanPoint bits)=
      tables.map (fun w => w (genericRowBitIndex n bits)) := by
  unfold functionalBatchCoefficients
  apply List.map_congr_left
  intro w hw
  exact generic_row_mle_boolean n w bits

/-- The functional is well-defined on the polynomial-family quotient.
At Boolean point b, extracting coefficient b gives the exact original
functional summand; summing yields equality without tuple uniqueness. -/
theorem functional_equivalence_well_defined (n : Nat) (tables : List (Nat → K))
    (left right : List (Poly K)) (equivalent : FunctionalBatchEquivalent n tables left right) :
    coefficientTableFunctional n tables left=coefficientTableFunctional n tables right := by
  unfold coefficientTableFunctional
  congr 1
  apply List.map_congr_left
  intro i hi
  obtain ⟨bits,index⟩ := packed_claim_lane_bits n i (List.mem_range.mp hi)
  have atBit := equivalent (genericRowBooleanPoint bits) i
  rw [functional_batch_boolean,index,weighted_lane_coefficient,weighted_lane_coefficient] at atBit
  exact atBit

/-- Stronger than per-obligation existence: the SAME lanes represent the source
family for every obligation and every later point. Cancellation noise is allowed;
no pointwise closeness of individual source lanes is required. -/
def SharedFunctionalRepresentative {Obligation : Type} (domain : List K)
    (n D R : Nat) (tables : Obligation → List (Nat → K)) (sources : List (K → K))
    (lanes : List (Poly K)) : Prop :=
  (∀ p∈lanes,p.DegLt D) ∧ sources.length=lanes.length ∧
    (∀ obligation,(tables obligation).length=lanes.length) ∧ ∀ obligation point,
    finiteRSMismatches domain
      (weightedVirtualOracle (functionalBatchCoefficients n (tables obligation) point) sources)
      (weightedLanePolynomial (functionalBatchCoefficients n (tables obligation) point) lanes).eval≤R

/-- Equivalence simultaneously preserves EVERY requested functional; this
still does not prove that a representative satisfying the full AIR exists. -/
theorem shared_functional_equivalence_well_defined {Obligation : Type}
    (n : Nat) (tables : Obligation → List (Nat → K)) (left right : List (Poly K))
    (equivalent : ∀ obligation,FunctionalBatchEquivalent n (tables obligation) left right) :
    ∀ obligation,coefficientTableFunctional n (tables obligation) left=
      coefficientTableFunctional n (tables obligation) right := by
  intro obligation
  exact functional_equivalence_well_defined n _ left right (equivalent obligation)

/-- Uniqueness only needs scalar-family closeness, not joint source closeness.
Coefficients, weights and candidate can all be chosen after earlier challenges;
the representative polynomial tuple remains fixed. -/
theorem scalar_representative_unique_candidate (domain : List K) (distinct : domain.Nodup)
    (coefficients : List K) (sources : List (K → K)) (lanes : List (Poly K))
    (D R T : Nat) (degrees : ∀ p∈lanes,p.DegLt D)
    (closeRepresentative : finiteRSMismatches domain (weightedVirtualOracle coefficients sources)
      (weightedLanePolynomial coefficients lanes).eval≤R)
    (threshold : T≤domain.length) (separation : R+(domain.length-T)+D≤domain.length)
    (candidate : Poly K) (degree : candidate.DegLt D)
    (agreement : T≤count domain (fun x => weightedVirtualOracle coefficients sources x=candidate.eval x)) :
    ∀ i,candidate.coeff i=(weightedLanePolynomial coefficients lanes).coeff i := by
  have partition := finite_rs_agreement_partition domain (weightedVirtualOracle coefficients sources) candidate.eval
  have close : finiteRSMismatches domain (weightedVirtualOracle coefficients sources) candidate.eval≤domain.length-T := by omega
  have zero := finite_rs_unique_candidate domain distinct (weightedVirtualOracle coefficients sources)
    candidate (weightedLanePolynomial coefficients lanes) D (domain.length-T) R degree
    (weighted_lane_degree coefficients lanes D degrees) close closeRepresentative (by omega)
  intro i
  have eq := zero i
  rw [Poly.coeff_sub] at eq
  grind

theorem scalar_representative_no_candidate (domain : List K) (distinct : domain.Nodup)
    (coefficients : List K) (sources : List (K → K)) (lanes : List (Poly K))
    (weights : List K) (claim : K) (D R T : Nat)
    (degrees : ∀ p∈lanes,p.DegLt D)
    (closeRepresentative : finiteRSMismatches domain (weightedVirtualOracle coefficients sources)
      (weightedLanePolynomial coefficients lanes).eval≤R)
    (threshold : T≤domain.length) (separation : R+(domain.length-T)+D≤domain.length)
    (wrong : weightedLaneValues coefficients (lanes.map (scalarRSResidual weights))≠claim) :
    ¬∃ candidate : Poly K,candidate.DegLt D ∧ scalarRSResidual weights candidate=claim ∧
      T≤count domain (fun x => weightedVirtualOracle coefficients sources x=candidate.eval x) := by
  rintro ⟨candidate,degree,residual,agreement⟩
  have equal := scalar_representative_unique_candidate domain distinct coefficients sources lanes D R T
    degrees closeRepresentative threshold separation candidate degree agreement
  have same := scalar_rs_residual_congr candidate (weightedLanePolynomial coefficients lanes) weights equal
  rw [weighted_lane_residual,residual] at same
  exact wrong same.symm

/-- The same tuple is used even when the obligation and point are selected
adaptively. This specializes the shared representative, not a fresh existential. -/
theorem shared_functional_no_candidate {Obligation : Type}
    (domain : List K) (distinct : domain.Nodup) (n D R T : Nat)
    (tables : Obligation → List (Nat → K)) (sources : List (K → K)) (lanes : List (Poly K))
    (representative : SharedFunctionalRepresentative domain n D R tables sources lanes)
    (obligation : Obligation) (point : Nat → K) (weights : List K) (claim : K)
    (threshold : T≤domain.length) (separation : R+(domain.length-T)+D≤domain.length)
    (wrong : weightedLaneValues (functionalBatchCoefficients n (tables obligation) point)
      (lanes.map (scalarRSResidual weights))≠claim) :
    ¬∃ candidate : Poly K,candidate.DegLt D ∧ scalarRSResidual weights candidate=claim ∧
      T≤count domain (fun x => weightedVirtualOracle
        (functionalBatchCoefficients n (tables obligation) point) sources x=candidate.eval x) :=
  scalar_representative_no_candidate domain distinct _ sources lanes weights claim D R T
    representative.1 (representative.2.2.2 obligation point) threshold separation wrong

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


/-- Direct bridge into the actual stage-zero folding candidate predicate. -/
theorem scalar_representative_no_initial {K : Type} [Field K]
    (N0 : Nat) (sizes degrees : Nat → Nat) (roots challenges : Nat → K)
    (oracles : Nat → Nat → K) (allWeights : Nat → List K) (claims : Nat → K)
    (coefficients : List K) (sources : List (K → K)) (lanes : List (Poly K)) (R T : Nat)
    (sizeInitial : sizes 0=N0)
    (domainDistinct : ((List.range N0).map (fun i => roots 0^i)).Nodup)
    (source : ∀ i<N0,oracles 0 i=weightedVirtualOracle coefficients sources (roots 0^i))
    (laneDegrees : ∀ p∈lanes,p.DegLt (degrees 0))
    (closeRepresentative : finiteRSMismatches ((List.range N0).map (fun i => roots 0^i))
      (weightedVirtualOracle coefficients sources) (weightedLanePolynomial coefficients lanes).eval≤R)
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
  apply scalar_representative_no_candidate ((List.range N0).map (fun i => roots 0^i)) domainDistinct
    coefficients sources lanes (allWeights 0) (claims 0) (degrees 0) R T laneDegrees closeRepresentative
    (by simpa using threshold) (by simpa using separation) wrong
  exact ⟨candidate,degree,residual,agreement⟩


end NearCompression
