import NearCompression.GeneralWeightedExtraction
import NearCompression.AdaptiveRoundBudget
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Fixed before the next polynomial message and challenge. No commitment
extraction or relation to a preceding transcript is implicit. -/
structure WeightedFoldPrefix (K : Type) where
  domain : List K
  weight : K → Nat
  bound : Nat
  degree : Nat
  threshold : Nat
  sourceEven : K → K
  sourceOdd : K → K
  evenWeights : List K
  oddWeights : List K
  claim : K

def WeightedFoldPrefix.Valid (s : WeightedFoldPrefix K) : Prop :=
  s.domain.Nodup ∧ (∀ x∈s.domain,s.weight x≤s.bound) ∧
    2*(s.domain.map s.weight).sum+s.bound*(s.degree-1)<3*s.threshold

/-- No sufficiently agreeing pair realizes the current coefficient claim.
Independent of the next prover message. -/
def WeightedFoldPrefix.Doomed (s : WeightedFoldPrefix K) : Prop :=
  ¬∃ even odd : Poly K,even.DegLt s.degree ∧ odd.DegLt s.degree ∧
    s.threshold≤consistencyMass s.domain s.weight
      (fun x=>s.sourceEven x=even.eval x ∧ s.sourceOdd x=odd.eval x) ∧
    scalarRSResidual s.evenWeights even+scalarRSResidual s.oddWeights odd=s.claim

/-- Invalid messages reject. The next candidate existential is inside the
challenge event, so candidates may depend on the challenge. -/
def weightedFoldEscape (s : WeightedFoldPrefix K) (sent : Poly K) (r : K) : Prop :=
  s.Doomed ∧ sent.DegLt 3 ∧ sent.eval 0+sent.eval 1=s.claim ∧
    generalWeightedCurveSuccess s.domain s.weight s.sourceEven s.sourceOdd
      s.degree s.threshold s.evenWeights s.oddWeights sent r

/-- Every fixed prefix and next prover message, in the existing stricter
three-candidate regime. No Johnson or quantum assertion. -/
theorem weighted_fold_prefix_escape_bound (s : WeightedFoldPrefix K)
    (valid : s.Valid) (sample : List K) (distinct : sample.Nodup) (sent : Poly K) :
    count sample (weightedFoldEscape s sent)≤max s.domain.length 2 := by
  classical
  by_cases doomed : s.Doomed
  · by_cases degree : sent.DegLt 3
    · by_cases endpoint : sent.eval 0+sent.eval 1=s.claim
      · have noOutcome : ¬∃ even odd : Poly K,even.DegLt s.degree ∧ odd.DegLt s.degree ∧
            s.threshold≤consistencyMass s.domain s.weight
              (fun x=>s.sourceEven x=even.eval x ∧ s.sourceOdd x=odd.eval x) ∧
            (sent-generalFoldResidualPolynomial s.evenWeights s.oddWeights even odd).IsZero := by
          rintro ⟨even,odd,he,ho,agree,eq⟩
          have zero := Poly.eval_of_isZero eq (0:K)
          have one := Poly.eval_of_isZero eq (1:K)
          rw [Poly.eval_sub] at zero one
          have endpoints := general_fold_residual_endpoints s.evenWeights s.oddWeights even odd
          apply doomed
          exact ⟨even,odd,he,ho,agree,by grind⟩
        have bound := general_weighted_extraction_bad_count s.domain sample valid.1 distinct
          s.weight s.bound s.degree s.threshold valid.2.1 s.sourceEven s.sourceOdd
          s.evenWeights s.oddWeights sent degree valid.2.2 noOutcome
        exact Nat.le_trans (count_mono sample (fun _ h=>h.2.2.2)) bound
      · simp [weightedFoldEscape,endpoint,count]
    · simp [weightedFoldEscape,degree,count]
  · simp [weightedFoldEscape,doomed,count]

/-- Full-history adaptive prefixes/messages. This bounds escape events, not
acceptance. Initial doom, terminal rejection and successive-state bindings
must be established separately for an actual protocol. -/
theorem weighted_fold_adaptive_escape_budget (sample : List K) (distinct : sample.Nodup)
    (states : List K→WeightedFoldPrefix K) (messages : List K→Poly K)
    (valid : ∀ history,(states history).Valid)
    (limit : Nat) (bounded : ∀ history,max (states history).domain.length 2≤limit)
    (history : List K) (rounds : Nat) :
    adaptiveFailureLeaves sample (fun h=>weightedFoldEscape (states h) (messages h)) history rounds*
      sample.length≤rounds*limit*sample.length^rounds := by
  have bounds : ∀ n h,AdaptiveRoundBounds sample
      (fun h=>weightedFoldEscape (states h) (messages h)) h (List.replicate n limit) := by
    intro n
    induction n with
    | zero => intro h; trivial
    | succ n ih =>
      intro h
      constructor
      · exact Nat.le_trans (weighted_fold_prefix_escape_bound (states h) (valid h)
          sample distinct (messages h)) (bounded h)
      · intro a ha; exact ih (h++[a])
  have result := adaptive_round_failure_budget sample
    (fun h=>weightedFoldEscape (states h) (messages h)) history (List.replicate rounds limit)
    (bounds rounds history)
  simpa using result

end NearCompression
