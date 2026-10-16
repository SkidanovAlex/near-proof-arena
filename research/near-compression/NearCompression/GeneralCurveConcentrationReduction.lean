import NearCompression.GeneralWeightedExtraction

/-! A sufficient concentration interface weaker than transferring every
postchallenge candidate to a prechallenge list. The concentration premise is
explicit and remains unproved in the list-decoding regime. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]
attribute [local instance] Classical.propDecidable

/-- Successes realized by one fixed affine polynomial curve. -/
def generalFixedCurveSuccess (domain : List K) (weight : K → Nat)
    (sourceEven sourceOdd : K → K) (T : Nat) (ew ow : List K)
    (sent even odd : Poly K) (r : K) : Prop :=
  T≤consistencyMass domain weight (fun x =>
    (1-r)*sourceEven x+r*sourceOdd x=(1-r)*even.eval x+r*odd.eval x) ∧
  (1-r)*scalarRSResidual ew (Poly.smul (1-r) even+Poly.smul r odd)+
    r*scalarRSResidual ow (Poly.smul (1-r) even+Poly.smul r odd)=sent.eval r

/-- More than max(|domain|,2) distinct successes on one curve force both joint
source agreement and the formal quadratic identity, with arbitrary weights. -/
theorem general_fixed_curve_many_outcome (domain sample : List K)
    (distinct : sample.Nodup) (weight : K → Nat) (sourceEven sourceOdd : K → K)
    (T : Nat) (ew ow : List K) (sent even odd : Poly K) (sentDegree : sent.DegLt 3)
    (many : max domain.length 2<count sample
      (generalFixedCurveSuccess domain weight sourceEven sourceOdd T ew ow sent even odd)) :
    T≤consistencyMass domain weight
      (fun x => sourceEven x=even.eval x ∧ sourceOdd x=odd.eval x) ∧
    (sent-generalFoldResidualPolynomial ew ow even odd).IsZero := by
  classical
  let good := sample.filter (fun r => decide
    (generalFixedCurveSuccess domain weight sourceEven sourceOdd T ew ow sent even odd r))
  have size : good.length=count sample
      (generalFixedCurveSuccess domain weight sourceEven sourceOdd T ew ow sent even odd) := by
    exact List.countP_eq_length_filter.symm
  apply general_shared_curve_extraction domain weight sourceEven sourceOdd (fun x => x)
    even odd sent ew ow T good (distinct.filter _)
  · rw [size]; exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) many
  · rw [size]; have h := Nat.le_max_right domain.length 2; omega
  · exact sentDegree
  · intro r hr
    exact (_root_.of_decide_eq_true (List.mem_filter.mp hr).2).1
  · intro r hr
    exact (_root_.of_decide_eq_true (List.mem_filter.mp hr).2).2

/-- Only one sufficiently populated curve is needed to bound the original
existential-candidate event. This does not prove the concentration premise. -/
theorem general_concentration_extraction_bad_count (domain sample : List K)
    (distinct : sample.Nodup) (weight : K → Nat) (sourceEven sourceOdd : K → K)
    (D T errorCount : Nat) (ew ow : List K) (sent : Poly K) (sentDegree : sent.DegLt 3)
    (concentration : errorCount<count sample
        (generalWeightedCurveSuccess domain weight sourceEven sourceOdd D T ew ow sent) →
      ∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
        max domain.length 2<count sample
          (generalFixedCurveSuccess domain weight sourceEven sourceOdd T ew ow sent even odd))
    (noOutcome : ¬∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
      T≤consistencyMass domain weight
        (fun x => sourceEven x=even.eval x ∧ sourceOdd x=odd.eval x) ∧
      (sent-generalFoldResidualPolynomial ew ow even odd).IsZero) :
    count sample (generalWeightedCurveSuccess domain weight sourceEven sourceOdd D T ew ow sent)≤errorCount := by
  classical
  apply Classical.byContradiction
  intro h
  obtain ⟨even,odd,de,do_,many⟩ := concentration (by omega)
  exact noOutcome ⟨even,odd,de,do_,general_fixed_curve_many_outcome domain sample distinct
    weight sourceEven sourceOdd T ew ow sent even odd sentDegree many⟩

end NearCompression
