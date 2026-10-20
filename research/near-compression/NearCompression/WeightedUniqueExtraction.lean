import NearCompression.WeightedThreeCandidate
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

noncomputable def weightedCurveSuccess (domain : List K) (weight : K → Nat)
    (sourceEven sourceOdd : K → K) (D T : Nat) (weights : List K)
    (w0 w1 : K) (sent : Poly K) (r : K) : Prop :=
  ∃ p : Poly K,p.DegLt D ∧ T≤consistencyMass domain weight
    (fun x => p.eval x=(1-r)*sourceEven x+r*sourceOdd x) ∧
    ((1-r)*w0+r*w1)*scalarRSResidual weights p=sent.eval r

/-- Actual existential-candidate concentration, in the stricter weighted
unique-decoding regime. The candidate existential is INSIDE the challenge
count. The resulting curve and quadratic identity are constructed, not assumed. -/
theorem weighted_unique_extraction_count (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (weight : K → Nat) (B D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (sourceEven sourceOdd : K → K) (weights : List K) (w0 w1 : K)
    (sent : Poly K) (sentDegree : sent.DegLt 3)
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T)
    (many : max domain.length 2<count sample
      (weightedCurveSuccess domain weight sourceEven sourceOdd D T weights w0 w1 sent)) :
    ∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
      T≤consistencyMass domain weight
        (fun x => sourceEven x=even.eval x ∧ sourceOdd x=odd.eval x) ∧
      (sent-weightedFoldResidualPolynomial w0 w1
        (scalarRSResidual weights even) (scalarRSResidual weights odd)).IsZero := by
  classical
  let success := weightedCurveSuccess domain weight sourceEven sourceOdd D T weights w0 w1 sent
  let good := sample.filter (fun r => decide (success r))
  have goodDistinct : good.Nodup := List.Sublist.nodup List.filter_sublist sampleDistinct
  have goodLength : good.length=count sample success := List.countP_eq_length_filter.symm
  have goodSuccess : ∀ r∈good,success r := by
    intro r hr
    exact of_decide_eq_true (List.mem_filter.mp hr).2
  let decoded : K → Poly K := fun r => if h : success r then Classical.choose h else Poly.zero
  have decodedCorrect : ∀ r∈good,(decoded r).DegLt D ∧
      T≤consistencyMass domain weight
        (fun x => (decoded r).eval x=(1-r)*sourceEven x+r*sourceOdd x) ∧
      ((1-r)*w0+r*w1)*scalarRSResidual weights (decoded r)=sent.eval r := by
    intro r hr
    have h := goodSuccess r hr
    have spec := Classical.choose_spec h
    simpa only [decoded,dite_eq_left h] using spec
  apply weighted_unique_regime_extraction domain domainDistinct weight B D T bounded
    sourceEven sourceOdd good goodDistinct
    (by rw [goodLength]; exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) many)
    (by
      rw [goodLength]
      change 3≤count sample (weightedCurveSuccess domain weight sourceEven sourceOdd D T weights w0 w1 sent)
      have h := Nat.le_max_right domain.length 2
      omega)
    decoded weights w0 w1 sent sentDegree
  · intro r hr; exact (decodedCorrect r hr).1
  · intro r hr; exact (decodedCorrect r hr).2.1
  · intro r hr; exact (decodedCorrect r hr).2.2
  · exact separation

/-- Explicit challenge-count error in this regime; no cryptographic premise. -/
theorem weighted_unique_extraction_bad_count (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (weight : K → Nat) (B D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (sourceEven sourceOdd : K → K) (weights : List K) (w0 w1 : K)
    (sent : Poly K) (sentDegree : sent.DegLt 3)
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T)
    (noOutcome : ¬∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
      T≤consistencyMass domain weight
        (fun x => sourceEven x=even.eval x ∧ sourceOdd x=odd.eval x) ∧
      (sent-weightedFoldResidualPolynomial w0 w1
        (scalarRSResidual weights even) (scalarRSResidual weights odd)).IsZero) :
    count sample (weightedCurveSuccess domain weight sourceEven sourceOdd D T weights w0 w1 sent)
      ≤max domain.length 2 := by
  have impossible : ¬max domain.length 2<count sample
      (weightedCurveSuccess domain weight sourceEven sourceOdd D T weights w0 w1 sent) := by
    intro many
    exact noOutcome (weighted_unique_extraction_count domain sample domainDistinct sampleDistinct
      weight B D T bounded sourceEven sourceOdd weights w0 w1 sent sentDegree separation many)
  omega

end NearCompression
