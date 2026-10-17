import NearCompression.VirtualSourceBatching
import NearCompression.ScalarRSTerminal

/-! Typed candidate relations for the initial Basefold batching reduction.
The RBR obligation below is a DEFINITION, not a proved theorem or an axiom.
The proved finite-family bound controls candidate claim cancellation only;
it does not supply correlated decoding or a small complete candidate family. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

structure FiniteBatchInstance (K : Type) [Field K] where
  domain : List K
  domainDistinct : domain.Nodup
  sources : List (K → K)
  claims : List K
  claimShape : claims.length=sources.length
  positiveLanes : 0<sources.length
  degree : Nat
  weights : List K
  weightShape : weights.length=degree
  threshold : Nat
  thresholdPositive : 0<threshold
  thresholdBound : threshold≤domain.length

noncomputable def finiteBatchJointAgreement (inst : FiniteBatchInstance K)
    (candidates : List (Poly K)) : Nat :=
  count inst.domain (fun x => ∀ lane, lane<inst.sources.length →
    (inst.sources.getD lane (fun _ => 0)) x=(candidates.getD lane Poly.zero).eval x)

def FiniteBatchCandidate (inst : FiniteBatchInstance K) (candidates : List (Poly K)) : Prop :=
  candidates.length=inst.sources.length ∧
  (∀ p∈candidates,p.DegLt inst.degree) ∧
  inst.threshold≤finiteBatchJointAgreement inst candidates ∧
  candidates.map (scalarRSResidual inst.weights)=inst.claims

def FiniteVirtualBatchCandidate (inst : FiniteBatchInstance K) (alpha : K)
    (candidate : Poly K) : Prop :=
  candidate.DegLt inst.degree ∧
  inst.threshold≤count inst.domain
    (fun x => virtualSourceOracle alpha inst.sources x=candidate.eval x) ∧
  scalarRSResidual inst.weights candidate=lanePowerBatch alpha inst.claims

/-- Mandatory unproved correlated-agreement reduction. `sample` must model
the uniform finite-field challenge space in its eventual instantiation.
No current theorem in this module discharges this obligation. -/
noncomputable def FiniteVirtualBatchRBRObligation (inst : FiniteBatchInstance K)
    (sample : List K) (errorCount : Nat) : Prop :=
  (¬ ∃ candidates, FiniteBatchCandidate inst candidates) →
    count sample (fun alpha => ∃ candidate, FiniteVirtualBatchCandidate inst alpha candidate)≤errorCount

private theorem finite_count_or {A : Type} (sample : List A) (p q : A → Prop) :
    count sample (fun a => p a ∨ q a)≤count sample p+count sample q := by
  classical
  induction sample with
  | nil => simp [count]
  | cons a rest ih =>
    simp only [count,List.countP_cons] at ih ⊢
    by_cases hp : p a <;> by_cases hq : q a <;> simp_all <;> omega

theorem finite_candidate_union_count {A B : Type} (sample : List A) (family : List B)
    (event : B → A → Prop) (bound : Nat)
    (each : ∀ candidate∈family,count sample (event candidate)≤bound) :
    count sample (fun a => ∃ candidate∈family,event candidate a)≤family.length*bound := by
  classical
  induction family with
  | nil => simp [count]
  | cons candidate rest ih =>
    have head := each candidate (List.mem_cons_self ..)
    have tail := ih (fun c hc => each c (List.mem_cons_of_mem _ hc))
    have union := finite_count_or sample (event candidate)
      (fun a => ∃ c∈rest,event c a)
    have predicate : (fun a => ∃ c∈candidate::rest,event c a)=
        (fun a => event candidate a ∨ ∃ c∈rest,event c a) := by
      funext a
      apply propext
      simp
    rw [predicate]
    simp only [List.length_cons,Nat.succ_mul]
    omega

/-- A fixed finite family of candidate claim vectors can switch with alpha,
but the resulting cancellation event still obeys an explicit union bound. -/
theorem finite_candidate_claim_cancellation (claims : List K) (L : Nat)
    (positive : 0<L) (shape : claims.length=L) (family : List (List K))
    (familyShape : ∀ values∈family,values.length=L)
    (wrong : ∀ values∈family,∃ lane,claims.getD lane 0≠values.getD lane 0)
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun alpha => ∃ values∈family,
      lanePowerBatch alpha claims=lanePowerBatch alpha values)≤family.length*(L-1) := by
  apply finite_candidate_union_count
  intro values member
  obtain ⟨lane,discrepancy⟩ := wrong values member
  exact lane_claim_batch_bad_count_le claims values L lane positive shape
    (familyShape values member) discrepancy sample distinct

/-- The finite family may consist of actual decoded polynomial tuples.
Only their concrete terminal linear-functional values enter cancellation.
This statement neither manufactures nor bounds such a candidate family. -/
theorem finite_polynomial_candidate_cancellation (claims weights : List K) (L : Nat)
    (positive : 0<L) (shape : claims.length=L) (family : List (List (Poly K)))
    (familyShape : ∀ candidates∈family,candidates.length=L)
    (wrong : ∀ candidates∈family,∃ lane,
      claims.getD lane 0≠(candidates.map (scalarRSResidual weights)).getD lane 0)
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun alpha => ∃ candidates∈family,
      lanePowerBatch alpha claims=
        lanePowerBatch alpha (candidates.map (scalarRSResidual weights)))≤family.length*(L-1) := by
  apply finite_candidate_union_count
  intro candidates member
  obtain ⟨lane,discrepancy⟩ := wrong candidates member
  exact lane_claim_batch_bad_count_le claims (candidates.map (scalarRSResidual weights)) L lane
    positive shape (by rw [List.length_map,familyShape candidates member]) discrepancy sample distinct

end NearCompression
