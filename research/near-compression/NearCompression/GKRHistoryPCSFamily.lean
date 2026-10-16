import NearCompression.GKRHistoryStrategy
import NearCompression.GKRJointFailureAcceptance
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

/-- Downstream messages indexed by concrete row coordinates and the final GKR
block. Within PCS, sent polynomials and folding oracles retain their causal
prefix arguments. Earlier GKR blocks may be captured by the family. -/
structure GKRBlockPCSFamily (K : Type) [Field K] where
  sent : List K → GKRBlock K → List K → Poly K
  claim : List K → GKRBlock K → List K → K
  constants : List K → GKRBlock K → List (Nat × K)
  prover : List K → GKRBlock K → List K → WeightedPrefixProver K

structure GKRHistoryPCSFamily (K : Type) [Field K] where
  sent : List K → List K → Poly K
  claim : List K → List K → K
  constants : List K → List (Nat × K)
  prover : List K → List K → WeightedPrefixProver K

def reindexGKRPCSFamily {K : Type} [Field K] (layout : GKRJointLayout)
    (family : GKRBlockPCSFamily K) : GKRHistoryPCSFamily K :=
  ⟨gkrHistoryReindex layout family.sent,gkrHistoryReindex layout family.claim,
    gkrHistoryReindex layout family.constants,gkrHistoryReindex layout family.prover⟩

theorem gkr_pcs_family_reindex {K : Type} [Field K]
    (layout : GKRJointLayout) (family : GKRBlockPCSFamily K) (rows : List K) (block : GKRBlock K)
    (rowLength : rows.length=layout.rowCoordinates)
    (leftLength : block.1.length=layout.inputLog) (rightLength : block.2.1.length=layout.inputLog) :
    let h := rows++gkrBlockCoordinates block
    (reindexGKRPCSFamily layout family).sent h=family.sent rows block ∧
    (reindexGKRPCSFamily layout family).claim h=family.claim rows block ∧
    (reindexGKRPCSFamily layout family).constants h=family.constants rows block ∧
    (reindexGKRPCSFamily layout family).prover h=family.prover rows block := by
  exact ⟨gkr_history_reindex_inverse layout _ rows block rowLength leftLength rightLength,
    gkr_history_reindex_inverse layout _ rows block rowLength leftLength rightLength,
    gkr_history_reindex_inverse layout _ rows block rowLength leftLength rightLength,
    gkr_history_reindex_inverse layout _ rows block rowLength leftLength rightLength⟩

def gkrBlockPCSChecks {K : Type} [Field K] [DecidableEq K]
    (layout : GKRJointLayout) (family : GKRBlockPCSFamily K) (roots : Nat → K) (sizes : Nat → Nat)
    (rows : List K) (block : GKRBlock K) (z path : List K) (queries : List Nat) : Prop :=
  weightedSumcheckChecks (family.sent rows block) (family.claim rows block) [] z ∧
  weightedReplayAccept z (family.claim rows block z) ((family.prover rows block z).messages layout.commonLog)
    (family.prover rows block z).terminal roots (family.prover rows block z).oracles sizes path queries

def gkrHistoryPCSChecks {K : Type} [Field K] [DecidableEq K]
    (layout : GKRJointLayout) (family : GKRHistoryPCSFamily K) (roots : Nat → K) (sizes : Nat → Nat)
    (h z path : List K) (queries : List Nat) : Prop :=
  weightedSumcheckChecks (family.sent h) (family.claim h) [] z ∧
  weightedReplayAccept z (family.claim h z) ((family.prover h z).messages layout.commonLog)
    (family.prover h z).terminal roots (family.prover h z).oracles sizes path queries

theorem gkr_pcs_checks_reindex {K : Type} [Field K] [DecidableEq K]
    (layout : GKRJointLayout) (family : GKRBlockPCSFamily K) (roots : Nat → K) (sizes : Nat → Nat)
    (rows : List K) (block : GKRBlock K) (z path : List K) (queries : List Nat)
    (rowLength : rows.length=layout.rowCoordinates)
    (leftLength : block.1.length=layout.inputLog) (rightLength : block.2.1.length=layout.inputLog) :
    gkrHistoryPCSChecks layout (reindexGKRPCSFamily layout family) roots sizes
      (rows++gkrBlockCoordinates block) z path queries ↔
    gkrBlockPCSChecks layout family roots sizes rows block z path queries := by
  have eqs := gkr_pcs_family_reindex layout family rows block rowLength leftLength rightLength
  unfold gkrHistoryPCSChecks gkrBlockPCSChecks
  rw [eqs.1,eqs.2.1,eqs.2.2.2]

/-- Initial private claim binding is preserved too: constant subtraction uses
exactly the original left/right/gamma and original final-layer messages. -/
theorem gkr_pcs_initial_reindex {K : Type} [Field K]
    (layout : GKRJointLayout) (family : GKRBlockPCSFamily K)
    (raw : List K → (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (earlier : List (GKRBlock K)) (rows : List K) (block : GKRBlock K)
    (rowLength : rows.length=layout.rowCoordinates)
    (leftLength : block.1.length=layout.inputLog) (rightLength : block.2.1.length=layout.inputLog) :
    let h := rows++gkrBlockCoordinates block
    (reindexGKRPCSFamily layout family).claim h []=
      gkrRemoveConstants layout.inputLog (gkrHistoryLeft layout h) (gkrHistoryRight layout h)
        (gkrHistoryGamma layout h) ((reindexGKRPCSFamily layout family).constants h)
        (gkrHistoryTerminalClaim layout raw earlier h) ↔
    family.claim rows block []=gkrRemoveConstants layout.inputLog
      (fun i => block.1.getD i 0) (fun i => block.2.1.getD i 0) block.2.2 (family.constants rows block)
      ((raw rows layout.inputLog earlier).a block.1 block.2.1+
        block.2.2*(raw rows layout.inputLog earlier).b block.1 block.2.1) := by
  dsimp only
  have eqs := gkr_pcs_family_reindex layout family rows block rowLength leftLength rightLength
  have axes := gkr_joint_history_accessors layout rows block rowLength leftLength rightLength
  rw [eqs.2.1,eqs.2.2.1,axes.1,axes.2.1,axes.2.2,
    gkr_history_terminal_claim_inverse layout raw earlier rows block rowLength leftLength rightLength]

/-- Concrete accepted terminal mismatch equals the history-indexed PCS event.
The source tuple must still be identified with the chosen representative,
and PCS source-oracle/authentication premises are not supplied by this identity. -/
theorem gkr_pcs_accepted_mismatch_reindex {K : Type} [Field K] [DecidableEq K]
    (layout : GKRJointLayout) (family : GKRBlockPCSFamily K) (roots : Nat → K) (sizes : Nat → Nat)
    (raw : List K → (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (layers : List (List GKRWiringGate)) (rounds : List Nat) (earlier : List (GKRBlock K))
    (rows : List K) (block : GKRBlock K) (z path : List K) (queries : List Nat)
    (rowLength : rows.length=layout.rowCoordinates)
    (leftLength : block.1.length=layout.inputLog) (rightLength : block.2.1.length=layout.inputLog)
    (entries : List (GKRSourceLane × Poly K))
    (checks : gkrEvaluatedVerifierPath (raw rows) layers [] (rounds++[layout.inputLog]) (earlier++[block])) :
    let h := rows++gkrBlockCoordinates block
    let inputs := gkrRecoveredCircuitInput layout.commonLog entries (gkrHistoryRowpoints layout h) (family.constants rows block)
    (gkrTerminalMismatch (gkrBindCircuitValues (raw rows) inputs layers) (gkrReverseCircuitValues inputs layers)
      1 [] (rounds++[layout.inputLog]) (earlier++[block]) ∧
      gkrBlockPCSChecks layout family roots sizes rows block z path queries) ↔
    (gkrHistoryTerminalClaim layout raw earlier h≠gkrInputFunctional layout.inputLog
      (gkrHistoryLeft layout h) (gkrHistoryRight layout h) (gkrHistoryGamma layout h)
      (gkrRecoveredCircuitInput layout.commonLog entries (gkrHistoryRowpoints layout h)
        ((reindexGKRPCSFamily layout family).constants h)) ∧
      gkrHistoryPCSChecks layout (reindexGKRPCSFamily layout family) roots sizes h z path queries) := by
  dsimp only
  have eqs := gkr_pcs_family_reindex layout family rows block rowLength leftLength rightLength
  have mismatch := gkr_history_strategy_terminal_event layout raw layers rounds earlier rows block
    rowLength leftLength rightLength entries (family.constants rows block) checks
  dsimp only at mismatch
  rw [eqs.2.2.1,mismatch,
    gkr_pcs_checks_reindex layout family roots sizes rows block z path queries rowLength leftLength rightLength]

end NearCompression
