import NearCompression.GKRFixedLayerLink
import NearCompression.GKRPathCount
namespace NearCompression
open Lean.Grind ArenaCore.Security
variable {K : Type} [Field K]

/-- Concrete circuit linkage along a verifier path. Circuit values and wiring
are fixed before the history; messages may depend on the prior history.
The final combined evaluation is exact here: a PCS binding theorem must establish them
before applying this relation to cryptographic acceptance. -/
def gkrCircuitCheckedToInput
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (values : Nat → Nat → K) (wiring : Nat → Nat → GKRWiringGate)
    (depth : Nat) (history : List (GKRBlock K)) : List Nat → List (GKRBlock K) → Prop
  | [],_ => False
  | _,[] => False
  | [m],[block] =>
      (strategy m history).values=values depth ∧
      (strategy m history).checked block ∧
      (strategy m history).a block.1 block.2.1+block.2.2*(strategy m history).b block.1 block.2.1=
        gkrQueryFunctional m (values depth)
          [(fun i => block.1.getD i 0,1),(fun i => block.2.1.getD i 0,block.2.2)]
  | m::n::rest,block::tail =>
      (strategy m history).values=values depth ∧
      (strategy m history).checked block ∧
      (strategy n (history++[block])).values=values (depth+1) ∧
      (strategy n (history++[block])).gates=gkrWeightedLayer m (wiring depth)
        [(fun i => block.1.getD i 0,1),(fun i => block.2.1.getD i 0,block.2.2)] ∧
      (∀ i,i<2^m → values depth i=gkrLayerValues (values (depth+1)) (wiring depth) i) ∧
      (strategy n (history++[block])).claimLeft []=
        (strategy m history).a block.1 block.2.1+block.2.2*(strategy m history).b block.1 block.2.1 ∧
      gkrCircuitCheckedToInput strategy values wiring (depth+1) (history++[block]) (n::rest) tail
  | _,_ => False

/-- Structural fixed-circuit checks discharge every abstract adjacent
correctness equivalence, and the exact combined terminal obligation discharges the final
functional. No per-layer soundness assumption is supplied. -/
theorem gkr_circuit_path_linked
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (values : Nat → Nat → K) (wiring : Nat → Nat → GKRWiringGate)
    (rounds : List Nat) (blocks history : List (GKRBlock K)) (depth : Nat)
    (checked : gkrCircuitCheckedToInput strategy values wiring depth history rounds blocks) :
    gkrCheckedToInput strategy history rounds blocks := by
  induction rounds generalizing history blocks depth with
  | nil => simp [gkrCircuitCheckedToInput] at checked
  | cons m rest ih =>
    cases blocks with
    | nil => simp [gkrCircuitCheckedToInput] at checked
    | cons block tail =>
      cases rest with
      | nil =>
        cases tail with
        | nil =>
          obtain ⟨fixed,checks,terminal⟩:=checked
          refine ⟨checks,?_⟩
          simpa only [GKRLayerStrategy.nextCorrect,fixed,gkr_next_queries] using terminal
        | cons _ _ => simp [gkrCircuitCheckedToInput] at checked
      | cons n rest =>
        cases tail with
        | nil => simp [gkrCircuitCheckedToInput] at checked
        | cons nextBlock tail =>
          obtain ⟨fixed,checks,nextFixed,queries,evaluation,claim,following⟩:=checked
          refine ⟨checks,?_,ih (nextBlock::tail) (history++[block]) (depth+1) following⟩
          apply gkr_fixed_layer_adjacent_correctness _ _ block (wiring depth) queries _ claim
          intro i hi
          rw [fixed,nextFixed]
          exact evaluation i hi

/-- Ideal uniform-challenge bound for fixed-circuit checked paths with exact
terminal evaluations. This does not replace PCS binding or Fiat-Shamir/QROM
analysis, and makes no quantum-security parameter claim. -/
theorem gkr_circuit_checked_path_budget (sample : List K) (distinct : sample.Nodup)
    (strategy : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (values : Nat → Nat → K) (wiring : Nat → Nat → GKRWiringGate)
    (rounds : List Nat) (history : List (GKRBlock K)) (depth : Nat)
    (wrong : ∀ m rest,rounds=m::rest → (strategy m history).wrong) :
    count (gkrChallengePaths sample rounds)
      (gkrCircuitCheckedToInput strategy values wiring depth history rounds)*sample.length≤
      (rounds.map (fun m => 4*m+1)).sum*(gkrChallengePaths sample rounds).length := by
  have subset : count (gkrChallengePaths sample rounds)
      (gkrCircuitCheckedToInput strategy values wiring depth history rounds)≤
      count (gkrChallengePaths sample rounds) (gkrCheckedToInput strategy history rounds) := by
    apply count_mono
    intro blocks checked
    exact gkr_circuit_path_linked strategy values wiring rounds blocks history depth checked
  exact Nat.le_trans (Nat.mul_le_mul_right sample.length subset)
    (gkr_linked_checked_path_budget sample distinct strategy rounds history wrong)
end NearCompression
