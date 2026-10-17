import NearCompression.GKRMessageCheck
import NearCompression.GKREvaluatedStrategy
import NearCompression.TerminalStoredRouteCheck
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K] [DecidableEq K]

/-- Check the actual message path, including next-layer query wiring and
claim linkage. Challenge derivation is deliberately outside this predicate. -/
def gkrPathMessageCheck
    (raw : (m : Nat)→List (GKRBlock K)→GKRLayerStrategy K m)
    (layers : List (List GKRWiringGate)) (history : List (GKRBlock K)) :
    List Nat→List (GKRBlock K)→Bool
  | [],_=>false
  | _,[]=>false
  | [m],[block]=>decide (history.length+1=layers.length) && gkrLayerMessageCheck (raw m history) block
  | m::n::rest,block::tail=>
      gkrLayerMessageCheck (raw m history) block &&
      decide (history.length+1<layers.length ∧
        2^m≤(layers.getD (layers.length-(history.length+2)) []).length ∧
        (raw n (history++[block])).gates=gkrWeightedLayer m
          (gkrReverseCircuitWiring layers (history.length+1))
          [(fun i=>block.1.getD i 0,1),(fun i=>block.2.1.getD i 0,block.2.2)] ∧
        (raw n (history++[block])).claimLeft []=
          (raw m history).a block.1 block.2.1+block.2.2*(raw m history).b block.1 block.2.1) &&
      gkrPathMessageCheck raw layers (history++[block]) (n::rest) tail
  | _,_=>false

theorem gkr_path_message_checked
    (raw : (m : Nat)→List (GKRBlock K)→GKRLayerStrategy K m)
    (layers : List (List GKRWiringGate)) (history : List (GKRBlock K))
    (rounds : List Nat) (blocks : List (GKRBlock K))
    (checked : gkrPathMessageCheck raw layers history rounds blocks=true) :
    gkrEvaluatedVerifierPath raw layers history rounds blocks := by
  induction rounds generalizing history blocks with
  | nil => simp [gkrPathMessageCheck] at checked
  | cons m rest ih =>
    cases blocks with
    | nil => simp [gkrPathMessageCheck] at checked
    | cons block tail =>
      cases rest with
      | nil =>
        cases tail with
        | nil =>
          simp only [gkrPathMessageCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
          exact ⟨checked.1,(gkr_layer_message_checked _ _ checked.2).2.2⟩
        | cons b bs => simp [gkrPathMessageCheck] at checked
      | cons n rest =>
        cases tail with
        | nil => simp [gkrPathMessageCheck] at checked
        | cons next tail =>
          simp only [gkrPathMessageCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
          exact ⟨(gkr_layer_message_checked _ _ checked.1.1).2.2,
            checked.1.2.1,checked.1.2.2.1,checked.1.2.2.2.1,checked.1.2.2.2.2,
            ih _ _ checked.2⟩

/-- Executable path checking discharges the semantic path assumption for the
fixed circuit input assignment used in the GKR soundness theorem. -/
theorem gkr_path_message_linked
    (raw : (m : Nat)→List (GKRBlock K)→GKRLayerStrategy K m)
    (inputs : Nat→K) (layers : List (List GKRWiringGate)) (history : List (GKRBlock K))
    (rounds : List Nat) (blocks : List (GKRBlock K))
    (checked : gkrPathMessageCheck raw layers history rounds blocks=true) :
    gkrCircuitVerifierPath (gkrBindCircuitValues raw inputs layers)
      (gkrReverseCircuitValues inputs layers) (gkrReverseCircuitWiring layers)
      (history.length+1) history rounds blocks :=
  gkr_evaluated_path_linked raw inputs layers rounds blocks history
    (gkr_path_message_checked raw layers history rounds blocks checked)
end NearCompression
