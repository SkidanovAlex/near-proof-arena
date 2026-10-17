import NearCompression.GKRCommonInputBoundary
import NearCompression.GenericLaneBatching
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

inductive GKRBinaryOp where | add | sub | mul
structure GKRWiringGate where
  op : GKRBinaryOp
  left : Nat
  right : Nat

def gkrGateValue (op : GKRBinaryOp) (a b : K) : K :=
  match op with | .add => a+b | .sub => a-b | .mul => a*b

/-- Literal weighted wiring expression after all u/v sumcheck rounds. -/
def gkrLayerWiring (m : Nat) (gates : List (GKRWiringGate × K))
    (ru rv : Nat → K) (a b : K) : K :=
  (gates.map (fun item => item.2*(rowEqualityWeight m ru item.1.left*
    rowEqualityWeight m rv item.1.right)*gkrGateValue item.1.op a b)).sum

/-- If the terminal sumcheck claim is still false but the actual wiring check
passes, at least one sent input evaluation is false. No polynomial-source
existence or layer correctness is assumed by this deterministic implication. -/
theorem gkr_wiring_false_inputs (m : Nat) (gates : List (GKRWiringGate × K))
    (ru rv values : Nat → K) (claim a b : K)
    (wrong : claim≠gkrLayerWiring m gates ru rv (genericRowMLE m values ru) (genericRowMLE m values rv))
    (checked : gkrLayerWiring m gates ru rv a b=claim) :
    a≠genericRowMLE m values ru ∨ b≠genericRowMLE m values rv := by
  by_cases ha : a=genericRowMLE m values ru
  · right
    intro hb
    rw [ha,hb] at checked
    exact wrong checked.symm
  · exact Or.inl ha

/-- One fresh gamma after BOTH a,b are fixed: a false terminal wiring claim
can turn into the correct next-layer claim for at most one sampled gamma.
The placement of a,b outside count is the causal commitment boundary. -/
theorem gkr_gamma_transition_bad_count (sample : List K) (distinct : sample.Nodup)
    (m : Nat) (gates : List (GKRWiringGate × K)) (ru rv values : Nat → K)
    (claim a b : K)
    (wrong : claim≠gkrLayerWiring m gates ru rv (genericRowMLE m values ru) (genericRowMLE m values rv)) :
    count sample (fun gamma => gkrLayerWiring m gates ru rv a b=claim ∧
      a+gamma*b=gkrInputFunctional m ru rv gamma values)≤1 := by
  by_cases checked : gkrLayerWiring m gates ru rv a b=claim
  · have different := gkr_wiring_false_inputs m gates ru rv values claim a b wrong checked
    have mismatch : ∃ i,([a,b]:List K).getD i 0≠
        ([genericRowMLE m values ru,genericRowMLE m values rv]:List K).getD i 0 := by
      rcases different with h | h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
    obtain ⟨i,hi⟩ := mismatch
    have roots := lane_claim_batch_bad_count [a,b] [genericRowMLE m values ru,genericRowMLE m values rv]
      2 i rfl rfl hi sample distinct
    have subset : count sample (fun gamma => gkrLayerWiring m gates ru rv a b=claim ∧
        a+gamma*b=gkrInputFunctional m ru rv gamma values)≤
        count sample (fun gamma => lanePowerBatch gamma [a,b]=
          lanePowerBatch gamma [genericRowMLE m values ru,genericRowMLE m values rv]) := by
      apply count_mono
      intro gamma h
      simp only [lanePowerBatch,gkrInputFunctional] at h ⊢
      grind
    omega
  · have empty : count sample (fun gamma => gkrLayerWiring m gates ru rv a b=claim ∧
        a+gamma*b=gkrInputFunctional m ru rv gamma values)=0 := by
      unfold count
      simp [checked]
    omega

/-- Known input constants are removed AFTER the same full-input functional;
subtracting their exact contribution preserves claim discrepancy. -/
theorem gkr_known_input_subtraction (m : Nat) (left right : Nat → K) (gamma claim : K)
    (privateValues known : Nat → K)
    (wrong : claim≠gkrInputFunctional m left right gamma (fun i => privateValues i+known i)) :
    claim-gkrInputFunctional m left right gamma known≠gkrInputFunctional m left right gamma privateValues := by
  intro equal
  apply wrong
  unfold gkrInputFunctional at equal ⊢
  rw [generic_row_mle_add,generic_row_mle_add]
  grind
end NearCompression
