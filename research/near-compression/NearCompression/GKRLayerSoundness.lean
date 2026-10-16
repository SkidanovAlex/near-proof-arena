import NearCompression.GKRAxisHistory
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Both actual axes compose without assuming honest wiring or an honest
round polynomial. Right-axis messages may depend on the complete left path,
but each right-round message depends only on its own preceding prefix. -/
theorem gkr_two_axes_false_persists (values : Nat → K) (gates : List (GKRWiringGate × K))
    (sentLeft : List K → Poly K) (claimLeft : List K → K)
    (sentRight : List K → List K → Poly K) (claimRight : List K → List K → K)
    (ru rv : List K) (shape : rv.length=ru.length)
    (leftBounds : ∀ item∈gates,item.1.left<2^ru.length)
    (rightBounds : ∀ item∈gates,item.1.right<2^ru.length)
    (wrong : claimLeft []≠(gates.map (fun item => item.2*gkrGateValue item.1.op
      (values item.1.left) (values item.1.right))).sum)
    (leftChecks : weightedSumcheckChecks sentLeft claimLeft [] ru)
    (reset : claimRight ru []=claimLeft ru)
    (rightChecks : weightedSumcheckChecks (sentRight ru) (claimRight ru) [] rv)
    (leftGood : ¬adaptivePathBad
      (gkrAdaptiveRoundBad values (gkrLeftAxisTerms values gates) sentLeft claimLeft) [] ru)
    (rightGood : ¬adaptivePathBad
      (gkrAdaptiveRoundBad values (gkrRightAxisTerms ru.length values (fun i => ru.getD i 0) gates)
        (sentRight ru) (claimRight ru)) [] rv) :
    claimRight ru rv≠gkrLayerWiring ru.length gates (fun i => ru.getD i 0) (fun i => rv.getD i 0)
      (genericRowMLE ru.length values (fun i => ru.getD i 0))
      (genericRowMLE ru.length values (fun i => rv.getD i 0)) := by
  have leftWrong : claimLeft []≠gkrStateClaim values (gkrLeftAxisTerms values gates) := by
    rwa [gkr_left_initial_claim]
  have afterLeft := gkr_adaptive_false_persists values (gkrLeftAxisTerms values gates)
    sentLeft claimLeft [] ru leftWrong leftChecks leftGood
  simp only [List.nil_append] at afterLeft
  rw [gkr_history_axis_reset values gates ru leftBounds] at afterLeft
  have rightWrong : claimRight ru []≠
      gkrStateClaim values (gkrRightAxisTerms ru.length values (fun i => ru.getD i 0) gates) := by
    rw [reset];exact afterLeft
  have afterRight := gkr_adaptive_false_persists values
    (gkrRightAxisTerms ru.length values (fun i => ru.getD i 0) gates)
    (sentRight ru) (claimRight ru) [] rv rightWrong rightChecks rightGood
  simp only [List.nil_append] at afterRight
  rw [gkr_history_terminal_wiring values gates ru rv shape rightBounds] at afterRight
  exact afterRight

/-- Conditional fresh-gamma error after the actual two-axis execution. Both
sent input evaluations are fixed before the gamma counted here. Axis bad-event
budgets must still be added for an unconditional complete-layer bound. -/
theorem gkr_two_axes_gamma_bad_count (sample : List K) (distinct : sample.Nodup)
    (values : Nat → K) (gates : List (GKRWiringGate × K))
    (sentLeft : List K → Poly K) (claimLeft : List K → K)
    (sentRight : List K → List K → Poly K) (claimRight : List K → List K → K)
    (ru rv : List K) (shape : rv.length=ru.length)
    (leftBounds : ∀ item∈gates,item.1.left<2^ru.length)
    (rightBounds : ∀ item∈gates,item.1.right<2^ru.length)
    (wrong : claimLeft []≠(gates.map (fun item => item.2*gkrGateValue item.1.op
      (values item.1.left) (values item.1.right))).sum)
    (leftChecks : weightedSumcheckChecks sentLeft claimLeft [] ru)
    (reset : claimRight ru []=claimLeft ru)
    (rightChecks : weightedSumcheckChecks (sentRight ru) (claimRight ru) [] rv)
    (leftGood : ¬adaptivePathBad
      (gkrAdaptiveRoundBad values (gkrLeftAxisTerms values gates) sentLeft claimLeft) [] ru)
    (rightGood : ¬adaptivePathBad
      (gkrAdaptiveRoundBad values (gkrRightAxisTerms ru.length values (fun i => ru.getD i 0) gates)
        (sentRight ru) (claimRight ru)) [] rv)
    (a b : K) :
    count sample (fun gamma =>
      gkrLayerWiring ru.length gates (fun i => ru.getD i 0) (fun i => rv.getD i 0) a b=claimRight ru rv ∧
      a+gamma*b=gkrInputFunctional ru.length (fun i => ru.getD i 0) (fun i => rv.getD i 0) gamma values)≤1 := by
  exact gkr_gamma_transition_bad_count sample distinct ru.length gates _ _ values (claimRight ru rv) a b
    (gkr_two_axes_false_persists values gates sentLeft claimLeft sentRight claimRight ru rv shape
      leftBounds rightBounds wrong leftChecks reset rightChecks leftGood rightGood)
end NearCompression
