import NearCompression.AdaptiveWeightedSumcheck
import NearCompression.WeightedSumcheckTerminal
import NearCompression.EqualityWeightResidual

/-! Close-case weighted sumcheck reduction for ONE fixed representative tuple.
The predicate uses the coefficient MLE directly; the equality-weight residual
representation can rewrite it without changing this finite counting theorem.
The tuple and tables precede the sumcheck randomness, not necessarily earlier
GKR randomness. No upstream AIR-witness soundness is inferred. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

theorem weighted_polynomial_mle (n : Nat) (coefficients : List K) (lanes : List (Poly K))
    (point : Nat → K) :
    genericRowMLE n (weightedLanePolynomial coefficients lanes).coeff point=
      weightedLaneValues coefficients (lanes.map (fun p => genericRowMLE n p.coeff point)) := by
  have zero : genericRowMLE n (Poly.zero : Poly K).coeff point=0 := by
    have same := generic_row_mle_congr n (Poly.zero : Poly K).coeff (fun _ => 0) point (by
      intro i hi
      simp [Poly.coeff,Poly.zero])
    exact same.trans (generic_row_mle_zero n point)
  induction coefficients generalizing lanes with
  | nil => exact zero
  | cons a as ih =>
    cases lanes with
    | nil => exact zero
    | cons p ps =>
      have coeffs : (weightedLanePolynomial (a::as) (p::ps)).coeff=
          (fun i => a*p.coeff i+(weightedLanePolynomial as ps).coeff i) := by
        funext i
        simp only [weightedLanePolynomial,Poly.coeff_add,Poly.coeff_smul]
      rw [coeffs,generic_row_mle_add,generic_row_mle_scale,ih]
      rfl

/-- Success of a close scalar candidate with the sent terminal coefficient-MLE
claim is a weighted-sumcheck false-to-true event. Adaptive choice of candidate
is allowed INSIDE each sampled path's existential. -/
theorem close_family_sumcheck_candidate_count (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (n D T : Nat) (tables : List (Nat → K)) (sources : List (K → K)) (lanes : List (Poly K))
    (representative : SharedFunctionalRepresentative domain n D (domain.length-T)
      (fun _ : Unit => tables) sources lanes)
    (threshold : T≤domain.length) (separation : 2*(domain.length-T)+D≤domain.length)
    (sent : List K → Poly K) (claim : List K → K)
    (wrong : claim []≠coefficientTableFunctional n tables lanes) :
    count (uniformTuples sample n) (fun path => weightedSumcheckChecks sent claim [] path ∧
      ∃ candidate : Poly K,candidate.DegLt D ∧
        genericRowMLE n candidate.coeff (fun i => path.getD i 0)=claim path ∧
        T≤count domain (fun x => weightedVirtualOracle
          (functionalBatchCoefficients n tables (fun i => path.getD i 0)) sources x=candidate.eval x)) *sample.length≤
      (2*n)*sample.length^n := by
  let xs := weightedLaneBlocks n (polynomialWeightLanes lanes tables)
  have shape : xs.length=(polynomialWeightLanes lanes tables).length*2^n := weighted_lane_blocks_shape n _
  have falseDot : claim []≠affineFoldDot xs := by
    rw [weighted_initial_functional]
    exact wrong
  have bound := adaptive_weighted_sumcheck_count sample sampleDistinct xs sent claim n
    (polynomialWeightLanes lanes tables).length shape falseDot
  have tupleLength : ∀ m : Nat,∀ path∈uniformTuples sample m,path.length=m := by
    intro m
    induction m with
    | zero => simp [uniformTuples]
    | succ m ih =>
      intro path hp
      simp only [uniformTuples,List.mem_flatMap,List.mem_map] at hp
      obtain ⟨r,hr,rest,hrest,rfl⟩ := hp
      simp [ih rest hrest]
  have subset : count (uniformTuples sample n) (fun path => weightedSumcheckChecks sent claim [] path ∧
      ∃ candidate : Poly K,candidate.DegLt D ∧
        genericRowMLE n candidate.coeff (fun i => path.getD i 0)=claim path ∧
        T≤count domain (fun x => weightedVirtualOracle
          (functionalBatchCoefficients n tables (fun i => path.getD i 0)) sources x=candidate.eval x))≤
      count (uniformTuples sample n) (fun path => weightedSumcheckChecks sent claim [] path ∧
        claim path=affineFoldDot (affineFoldFinal xs path)) := by
    classical
    unfold count
    apply List.countP_mono_left
    intro path hp success
    have accepted := @_root_.of_decide_eq_true _ (Classical.propDecidable _) success
    obtain ⟨checks,candidate,degree,residual,agreement⟩ := accepted
    have unique := scalar_representative_unique_candidate domain domainDistinct
      (functionalBatchCoefficients n tables (fun i => path.getD i 0)) sources lanes D (domain.length-T) T
      representative.1 (representative.2.2.2 () (fun i => path.getD i 0)) threshold (by omega)
      candidate degree agreement
    have mle := generic_row_mle_congr n candidate.coeff
      (weightedLanePolynomial (functionalBatchCoefficients n tables (fun i => path.getD i 0)) lanes).coeff
      (fun i => path.getD i 0) (fun i hi => unique i)
    rw [weighted_polynomial_mle,residual] at mle
    have terminal := weighted_terminal_beta path lanes tables
    rw [tupleLength n path hp] at terminal
    apply @_root_.decide_eq_true _ (Classical.propDecidable _)
    exact ⟨checks,mle.trans terminal.symm⟩
  exact Nat.le_trans (Nat.mul_le_mul_right sample.length subset) bound

/-- Same close-case bound with the ACTUAL equality-weight residual accepted by
the following folding protocol, rather than an abstract terminal predicate. -/
theorem close_family_sumcheck_residual_count (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (n D T : Nat) (tables : List (Nat → K)) (sources : List (K → K)) (lanes : List (Poly K))
    (representative : SharedFunctionalRepresentative domain n D (domain.length-T)
      (fun _ : Unit => tables) sources lanes)
    (threshold : T≤domain.length) (separation : 2*(domain.length-T)+D≤domain.length)
    (sent : List K → Poly K) (claim : List K → K)
    (wrong : claim []≠coefficientTableFunctional n tables lanes) :
    count (uniformTuples sample n) (fun path => weightedSumcheckChecks sent claim [] path ∧
      ∃ candidate : Poly K,candidate.DegLt D ∧
        scalarRSResidual (equalityWeights path) candidate=claim path ∧
        T≤count domain (fun x => weightedVirtualOracle
          (functionalBatchCoefficients n tables (fun i => path.getD i 0)) sources x=candidate.eval x)) *sample.length≤
      (2*n)*sample.length^n := by
  have bound := close_family_sumcheck_candidate_count domain sample domainDistinct sampleDistinct
    n D T tables sources lanes representative threshold separation sent claim wrong
  have tupleLength : ∀ m : Nat,∀ path∈uniformTuples sample m,path.length=m := by
    intro m
    induction m with
    | zero => simp [uniformTuples]
    | succ m ih =>
      intro path hp
      simp only [uniformTuples,List.mem_flatMap,List.mem_map] at hp
      obtain ⟨r,hr,rest,hrest,rfl⟩ := hp
      simp [ih rest hrest]
  have subset : count (uniformTuples sample n) (fun path => weightedSumcheckChecks sent claim [] path ∧
      ∃ candidate : Poly K,candidate.DegLt D ∧
        scalarRSResidual (equalityWeights path) candidate=claim path ∧
        T≤count domain (fun x => weightedVirtualOracle
          (functionalBatchCoefficients n tables (fun i => path.getD i 0)) sources x=candidate.eval x))≤
      count (uniformTuples sample n) (fun path => weightedSumcheckChecks sent claim [] path ∧
      ∃ candidate : Poly K,candidate.DegLt D ∧
        genericRowMLE n candidate.coeff (fun i => path.getD i 0)=claim path ∧
        T≤count domain (fun x => weightedVirtualOracle
          (functionalBatchCoefficients n tables (fun i => path.getD i 0)) sources x=candidate.eval x)) := by
    classical
    unfold count
    apply List.countP_mono_left
    intro path hp h
    have accepted := @_root_.of_decide_eq_true _ (Classical.propDecidable _) h
    obtain ⟨checks,candidate,degree,residual,agreement⟩ := accepted
    rw [scalar_residual_eq_weights_mle,tupleLength n path hp] at residual
    exact @_root_.decide_eq_true _ (Classical.propDecidable _) ⟨checks,candidate,degree,residual,agreement⟩
  exact Nat.le_trans (Nat.mul_le_mul_right sample.length subset) bound

end NearCompression
