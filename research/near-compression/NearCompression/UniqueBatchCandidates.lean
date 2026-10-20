import NearCompression.FiniteRSUniqueDecoding
import NearCompression.FiniteBatchCandidates

/-! Unique-decoding basin for arbitrary source oracles. The jointly-close
lane tuple is fixed before alpha. Decoded scalar candidates may depend on alpha.
Existence of the fixed tuple remains a premise; no far-source theorem is claimed. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def jointLaneMismatch (sources : List (K → K)) (lanes : List (Poly K)) (x : K) : Prop :=
  sources.map (fun f => f x) ≠ lanes.map (fun p => p.eval x)

theorem lane_polynomial_batch_degree (alpha : K) (lanes : List (Poly K)) (D : Nat)
    (degrees : ∀ p∈lanes,p.DegLt D) : (lanePolynomialBatch alpha lanes).DegLt D := by
  induction lanes with
  | nil => intro i hi; simp [lanePolynomialBatch,Poly.coeff,Poly.zero]
  | cons p ps ih =>
    exact Poly.degLt_add (degrees p (by simp))
      (Poly.degLt_smul alpha (ih (fun q hq => degrees q (by simp [hq]))))

theorem lane_polynomial_batch_residual (alpha : K) (lanes : List (Poly K)) (weights : List K) :
    scalarRSResidual weights (lanePolynomialBatch alpha lanes)=
      lanePowerBatch alpha (lanes.map (scalarRSResidual weights)) := by
  induction lanes with
  | nil =>
    simp only [lanePolynomialBatch,List.map_nil,lanePowerBatch,scalarRSResidual]
    generalize 0 = offset
    induction weights generalizing offset with
    | nil => rfl
    | cons w ws ih =>
      change w*Poly.zero.coeff offset+scalarRSResidualFrom Poly.zero (offset+1) ws=0
      rw [ih]
      simp only [Poly.coeff,Poly.zero,List.getD_nil]; grind
  | cons p ps ih =>
    simp only [lanePolynomialBatch,scalar_rs_residual_add,scalar_rs_residual_scale,
      List.map_cons,lanePowerBatch,ih]

theorem virtual_batch_joint_distance (domain : List K) (sources : List (K → K))
    (lanes : List (Poly K)) (alpha : K) :
    finiteRSMismatches domain (virtualSourceOracle alpha sources)
      (lanePolynomialBatch alpha lanes).eval ≤ count domain (jointLaneMismatch sources lanes) := by
  apply count_mono
  intro x mismatch
  intro equal
  apply mismatch
  rw [lane_polynomial_batch_eval]
  exact congrArg (lanePowerBatch alpha) equal

/-- Candidate choice is after alpha, but uniqueness forces the fixed batch. -/
theorem unique_virtual_batch_candidate (domain : List K) (distinct : domain.Nodup)
    (sources : List (K → K)) (lanes : List (Poly K)) (D R r : Nat)
    (degrees : ∀ p∈lanes,p.DegLt D)
    (jointClose : count domain (jointLaneMismatch sources lanes)≤R)
    (separation : R+r+D≤domain.length) (alpha : K) (candidate : Poly K)
    (degree : candidate.DegLt D)
    (close : finiteRSMismatches domain (virtualSourceOracle alpha sources) candidate.eval≤r) :
    ∀ i,candidate.coeff i=(lanePolynomialBatch alpha lanes).coeff i := by
  have closeBatch := Nat.le_trans (virtual_batch_joint_distance domain sources lanes alpha) jointClose
  have zero := finite_rs_unique_candidate domain distinct (virtualSourceOracle alpha sources)
    candidate (lanePolynomialBatch alpha lanes) D r R degree
    (lane_polynomial_batch_degree alpha lanes D degrees) close closeBatch (by omega)
  intro i
  have eq := zero i
  rw [Poly.coeff_sub] at eq
  grind

/-- Wrong-claim count in the unique-decoding basin, allowing adaptive candidates. -/
theorem unique_virtual_batch_bad_count (domain : List K) (distinct : domain.Nodup)
    (sources : List (K → K)) (lanes : List (Poly K)) (claims weights : List K)
    (D R r L lane : Nat) (positive : 0<L)
    (claimShape : claims.length=L) (laneShape : lanes.length=L)
    (degrees : ∀ p∈lanes,p.DegLt D)
    (jointClose : count domain (jointLaneMismatch sources lanes)≤R)
    (separation : R+r+D≤domain.length)
    (wrong : claims.getD lane 0≠(lanes.map (scalarRSResidual weights)).getD lane 0)
    (sample : List K) (sampleDistinct : sample.Nodup) :
    count sample (fun alpha => ∃ candidate : Poly K,
      candidate.DegLt D ∧
      finiteRSMismatches domain (virtualSourceOracle alpha sources) candidate.eval≤r ∧
      scalarRSResidual weights candidate=lanePowerBatch alpha claims)≤L-1 := by
  have collision := lane_claim_batch_bad_count_le claims (lanes.map (scalarRSResidual weights))
    L lane positive claimShape (by simpa using laneShape) wrong sample sampleDistinct
  apply Nat.le_trans _ collision
  apply count_mono
  intro alpha event
  obtain ⟨candidate,degree,close,claim⟩ := event
  have eq := unique_virtual_batch_candidate domain distinct sources lanes D R r degrees
    jointClose separation alpha candidate degree close
  have residual := scalar_rs_residual_congr candidate (lanePolynomialBatch alpha lanes) weights eq
  rw [lane_polynomial_batch_residual] at residual
  exact claim.symm.trans residual

end NearCompression
