import NearCompression.GKRCheckedPath
import NearCompression.GKROutputWeights
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- Honest adjacent-layer equality follows from the fixed gate evaluation and
actual next-query weights. Only the finite padded layer domain must agree. -/
theorem gkr_weighted_adjacent_functional (m : Nat) (inputs outputs : Nat → K)
    (gates : Nat → GKRWiringGate) (left right : Nat → K) (gamma : K)
    (evaluation : ∀ i,i<2^m → outputs i=gkrLayerValues inputs gates i) :
    ((gkrWeightedLayer m gates [(left,1),(right,gamma)]).map
      (fun item => item.2*gkrGateValue item.1.op
        (inputs item.1.left) (inputs item.1.right))).sum=
      gkrInputFunctional m left right gamma outputs := by
  have h:=gkr_layer_initial_queries m inputs gates [(left,1),(right,gamma)]
  rw [gkr_left_initial_claim,gkr_next_queries] at h
  rw [h]
  unfold gkrInputFunctional
  rw [generic_row_mle_congr m (gkrLayerValues inputs gates) outputs left
    (by intro i hi;exact (evaluation i hi).symm),
    generic_row_mle_congr m (gkrLayerValues inputs gates) outputs right
    (by intro i hi;exact (evaluation i hi).symm)]

/-- Discharges the honest-functional premise of adjacent correctness using
actual layer wiring and query construction. Transmitted claim equality remains
an explicit verifier check; fixed layer evaluation is a circuit identity. -/
theorem gkr_fixed_layer_adjacent_correctness {m n : Nat}
    (s : GKRLayerStrategy K m) (next : GKRLayerStrategy K n)
    (block : GKRBlock K) (wiring : Nat → GKRWiringGate)
    (queries : next.gates=gkrWeightedLayer m wiring
      [(fun i => block.1.getD i 0,1),(fun i => block.2.1.getD i 0,block.2.2)])
    (evaluation : ∀ i,i<2^m → s.values i=gkrLayerValues next.values wiring i)
    (claim : next.claimLeft []=s.a block.1 block.2.1+block.2.2*s.b block.1 block.2.1) :
    s.nextCorrect block ↔ ¬next.wrong := by
  apply gkr_adjacent_correctness s next block claim
  rw [queries]
  exact gkr_weighted_adjacent_functional m next.values s.values wiring _ _ _ evaluation
end NearCompression
