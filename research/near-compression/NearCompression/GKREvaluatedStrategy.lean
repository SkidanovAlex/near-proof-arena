import NearCompression.GKRRecoveredCircuit
namespace NearCompression
open Lean.Grind ArenaCore.Security
variable {K : Type} [Field K]

/-- Replace only the analysis assignment. All prover messages, wiring and
within-layer adaptive strategies are retained unchanged. -/
def gkrBindCircuitValues (raw : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (inputs : Nat → K) (layers : List (List GKRWiringGate))
    (m : Nat) (history : List (GKRBlock K)) : GKRLayerStrategy K m :=
  { raw m history with values := gkrReverseCircuitValues inputs layers (history.length+1) }

/-- The verifier's message checks do not read the analysis-only assignment. -/
theorem gkr_bind_values_preserves_checks
    (raw : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (inputs : Nat → K) (layers : List (List GKRWiringGate))
    (m : Nat) (history : List (GKRBlock K)) (block : GKRBlock K) :
    (gkrBindCircuitValues raw inputs layers m history).checked block ↔
      (raw m history).checked block := Iff.rfl

/-- Structural finite-circuit path checks. Values are computed, not separately
supplied. Shape, next-layer query wiring and transmitted-claim linkage remain
explicit; executable compiler/verifier refinement must establish these checks. -/
def gkrEvaluatedVerifierPath
    (raw : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (layers : List (List GKRWiringGate)) (history : List (GKRBlock K)) :
    List Nat → List (GKRBlock K) → Prop
  | [],_ => False
  | _,[] => False
  | [m],[block] => history.length+1=layers.length ∧ (raw m history).checked block
  | m::n::rest,block::tail =>
      (raw m history).checked block ∧ history.length+1<layers.length ∧
      2^m≤(layers.getD (layers.length-(history.length+2)) []).length ∧
      (raw n (history++[block])).gates=gkrWeightedLayer m
        (gkrReverseCircuitWiring layers (history.length+1))
        [(fun i => block.1.getD i 0,1),(fun i => block.2.1.getD i 0,block.2.2)] ∧
      (raw n (history++[block])).claimLeft []=
        (raw m history).a block.1 block.2.1+block.2.2*(raw m history).b block.1 block.2.1 ∧
      gkrEvaluatedVerifierPath raw layers (history++[block]) (n::rest) tail
  | _,_ => False

/-- Accepted structural paths consume exactly the remaining circuit layers. -/
theorem gkr_evaluated_path_shape
    (raw : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (layers : List (List GKRWiringGate)) (rounds : List Nat)
    (blocks history : List (GKRBlock K))
    (checks : gkrEvaluatedVerifierPath raw layers history rounds blocks) :
    blocks.length=rounds.length ∧ history.length+rounds.length=layers.length := by
  induction rounds generalizing blocks history with
  | nil => simp [gkrEvaluatedVerifierPath] at checks
  | cons m rest ih =>
    cases blocks with
    | nil => simp [gkrEvaluatedVerifierPath] at checks
    | cons block tail =>
      cases rest with
      | nil =>
        cases tail with
        | nil => exact ⟨rfl,checks.1⟩
        | cons _ _ => simp [gkrEvaluatedVerifierPath] at checks
      | cons n rest =>
        cases tail with
        | nil => simp [gkrEvaluatedVerifierPath] at checks
        | cons nextBlock tail =>
          have next := ih (nextBlock::tail) (history++[block]) checks.2.2.2.2.2
          simp only [List.length_append,List.length_cons,List.length_nil] at next ⊢
          omega

/-- Computed finite-circuit values discharge all adjacent evaluation and
per-layer assignment premises of the existing verifier-path relation. -/
theorem gkr_evaluated_path_linked
    (raw : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (inputs : Nat → K) (layers : List (List GKRWiringGate))
    (rounds : List Nat) (blocks history : List (GKRBlock K))
    (checks : gkrEvaluatedVerifierPath raw layers history rounds blocks) :
    gkrCircuitVerifierPath (gkrBindCircuitValues raw inputs layers)
      (gkrReverseCircuitValues inputs layers) (gkrReverseCircuitWiring layers)
      (history.length+1) history rounds blocks := by
  induction rounds generalizing blocks history with
  | nil => simp [gkrEvaluatedVerifierPath] at checks
  | cons m rest ih =>
    cases blocks with
    | nil => simp [gkrEvaluatedVerifierPath] at checks
    | cons block tail =>
      cases rest with
      | nil =>
        cases tail with
        | nil => exact ⟨rfl,checks.2⟩
        | cons _ _ => simp [gkrEvaluatedVerifierPath] at checks
      | cons n rest =>
        cases tail with
        | nil => simp [gkrEvaluatedVerifierPath] at checks
        | cons nextBlock tail =>
          obtain ⟨checked,depth,shape,queries,claim,following⟩ := checks
          refine ⟨rfl,checked,?_,queries,?_,claim,?_⟩
          · simp [gkrBindCircuitValues]
          · intro i hi
            apply gkr_reverse_circuit_step inputs layers (history.length+1) depth i
            simpa [Nat.add_assoc] using Nat.lt_of_lt_of_le hi shape
          · simpa using ih (nextBlock::tail) (history++[block]) following

/-- False-root acceptance budget for the constructed assignment. No caller
supplies independent layer values or adjacent evaluation equalities. Later
PCS checks remain in accepted, and their terminal-error count remains explicit. -/
theorem gkr_evaluated_continuation_budget {R : Type}
    (sample : List K) (distinct : sample.Nodup)
    (raw : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (inputs : Nat → K) (layers : List (List GKRWiringGate))
    (rounds : List Nat) (history : List (GKRBlock K))
    (continuations : List R) (accepted : List (GKRBlock K) → R → Prop)
    (checks : ∀ blocks r,accepted blocks r → gkrEvaluatedVerifierPath raw layers history rounds blocks)
    (wrong : ∀ m rest,rounds=m::rest → (gkrBindCircuitValues raw inputs layers m history).wrong) :
    let experiment := (gkrChallengePaths sample rounds).flatMap
      (fun blocks => continuations.map (fun r => (blocks,r)))
    count experiment (fun pair => accepted pair.1 pair.2)*sample.length≤
      (rounds.map (fun m => 4*m+1)).sum*(gkrChallengePaths sample rounds).length*continuations.length+
      count experiment (fun pair => accepted pair.1 pair.2 ∧
        gkrTerminalMismatch (gkrBindCircuitValues raw inputs layers) (gkrReverseCircuitValues inputs layers)
          (history.length+1) history rounds pair.1)*sample.length := by
  apply gkr_continuation_terminal_error_budget sample distinct (gkrBindCircuitValues raw inputs layers)
    (gkrReverseCircuitValues inputs layers) (gkrReverseCircuitWiring layers) rounds history
    (history.length+1) continuations accepted _ wrong
  intro blocks r accept
  exact gkr_evaluated_path_linked raw inputs layers rounds blocks history (checks blocks r accept)

/-- Structural path checks discharge both endpoint shape and recovered input
assignment. The mismatch is the full claim charged by the merged PCS theorem. -/
theorem gkr_evaluated_path_recovered_mismatch
    (raw : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (layers : List (List GKRWiringGate)) (rounds : List Nat)
    (blocks history : List (GKRBlock K)) (block : GKRBlock K)
    (layout : GKRJointLayout) (entries : List (GKRSourceLane × ZkFormal.Algebra.Poly K))
    (rowpoints : GKRSourceLane → Nat → K) (constants : List (Nat × K))
    (checks : gkrEvaluatedVerifierPath raw layers history
      (rounds++[layout.inputLog]) (blocks++[block])) :
    let inputs := gkrRecoveredCircuitInput layout.commonLog entries rowpoints constants
    gkrTerminalMismatch (gkrBindCircuitValues raw inputs layers) (gkrReverseCircuitValues inputs layers)
      (history.length+1) history (rounds++[layout.inputLog]) (blocks++[block]) ↔
      (raw layout.inputLog (history++blocks)).a block.1 block.2.1+
        block.2.2*(raw layout.inputLog (history++blocks)).b block.1 block.2.1≠
      gkrInputFunctional layout.inputLog (fun i => block.1.getD i 0) (fun i => block.2.1.getD i 0)
        block.2.2 inputs := by
  have shape := gkr_evaluated_path_shape raw layers (rounds++[layout.inputLog])
    (blocks++[block]) history checks
  simp only [List.length_append,List.length_cons,List.length_nil] at shape
  exact gkr_evaluated_recovered_terminal_mismatch _ layers rounds blocks history
    (by omega) (history.length+1) (by omega) block layout entries rowpoints constants

end NearCompression
