import NearCompression.GKRJointTerminalEvent
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

/-- Decode the final GKR block from the PCS chronological-history argument.
This is total on malformed histories, but inverse lemmas require exact lengths. -/
def gkrHistoryBlock {K : Type} [Field K] (layout : GKRJointLayout) (h : List K) : GKRBlock K :=
  ((h.drop layout.rowCoordinates).take layout.inputLog,
   ((h.drop layout.rowCoordinates).drop layout.inputLog).take layout.inputLog,
   gkrHistoryGamma layout h)

theorem gkr_history_block_inverse {K : Type} [Field K]
    (layout : GKRJointLayout) (rows : List K) (block : GKRBlock K)
    (rowLength : rows.length=layout.rowCoordinates)
    (leftLength : block.1.length=layout.inputLog) (rightLength : block.2.1.length=layout.inputLog) :
    (rows++gkrBlockCoordinates block).take layout.rowCoordinates=rows ∧
    gkrHistoryBlock layout (rows++gkrBlockCoordinates block)=block := by
  have rowTake : (rows++gkrBlockCoordinates block).take layout.rowCoordinates=rows := by
    rw [←rowLength];exact List.take_append_length
  have rowDrop : (rows++gkrBlockCoordinates block).drop layout.rowCoordinates=gkrBlockCoordinates block := by
    rw [←rowLength];exact List.drop_append_length
  refine ⟨rowTake,?_⟩
  have gamma := (gkr_joint_history_accessors layout rows block rowLength leftLength rightLength).2.2
  unfold gkrHistoryBlock
  rw [rowDrop,gamma]
  rcases block with ⟨left,right,g⟩
  dsimp only at leftLength rightLength ⊢
  unfold gkrBlockCoordinates
  have leftTake : (left++(right++[g])).take layout.inputLog=left := by
    rw [←leftLength];exact List.take_append_length
  have leftDrop : (left++(right++[g])).drop layout.inputLog=right++[g] := by
    rw [←leftLength];exact List.drop_append_length
  have rightTake : (right++[g]).take layout.inputLog=right := by
    rw [←rightLength];exact List.take_append_length
  simp only [List.append_assoc,leftTake,leftDrop,rightTake]

/-- Reindex an arbitrary downstream family. The result type can itself be a
history-dependent sent polynomial, claim function or folding prover. No
independence of those messages from earlier coordinates is introduced. -/
def gkrHistoryReindex {K A : Type} [Field K] (layout : GKRJointLayout)
    (family : List K → GKRBlock K → A) (h : List K) : A :=
  family (h.take layout.rowCoordinates) (gkrHistoryBlock layout h)

theorem gkr_history_reindex_inverse {K A : Type} [Field K]
    (layout : GKRJointLayout) (family : List K → GKRBlock K → A)
    (rows : List K) (block : GKRBlock K)
    (rowLength : rows.length=layout.rowCoordinates)
    (leftLength : block.1.length=layout.inputLog) (rightLength : block.2.1.length=layout.inputLog) :
    gkrHistoryReindex layout family (rows++gkrBlockCoordinates block)=family rows block := by
  have inverse := gkr_history_block_inverse layout rows block rowLength leftLength rightLength
  unfold gkrHistoryReindex
  rw [inverse.1,inverse.2]

/-- Construct the terminalClaim family required by the merged PCS theorem
from the actual last-layer a/b messages and fixed earlier GKR sequence. -/
def gkrHistoryTerminalClaim {K : Type} [Field K] (layout : GKRJointLayout)
    (raw : List K → (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (earlier : List (GKRBlock K)) : List K → K :=
  gkrHistoryReindex layout (fun rows block =>
    (raw rows layout.inputLog earlier).a block.1 block.2.1+
      block.2.2*(raw rows layout.inputLog earlier).b block.1 block.2.1)

theorem gkr_history_terminal_claim_inverse {K : Type} [Field K]
    (layout : GKRJointLayout)
    (raw : List K → (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (earlier : List (GKRBlock K)) (rows : List K) (block : GKRBlock K)
    (rowLength : rows.length=layout.rowCoordinates)
    (leftLength : block.1.length=layout.inputLog) (rightLength : block.2.1.length=layout.inputLog) :
    gkrHistoryTerminalClaim layout raw earlier (rows++gkrBlockCoordinates block)=
      (raw rows layout.inputLog earlier).a block.1 block.2.1+
        block.2.2*(raw rows layout.inputLog earlier).b block.1 block.2.1 :=
  gkr_history_reindex_inverse layout _ rows block rowLength leftLength rightLength

/-- Evaluated GKR mismatch is now stated with a constructed history-indexed
terminal claim, not an assumed equality to an unrelated claim function. -/
theorem gkr_history_strategy_terminal_event {K : Type} [Field K]
    (layout : GKRJointLayout)
    (raw : List K → (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (layers : List (List GKRWiringGate)) (rounds : List Nat)
    (earlier : List (GKRBlock K)) (rows : List K) (block : GKRBlock K)
    (rowLength : rows.length=layout.rowCoordinates)
    (leftLength : block.1.length=layout.inputLog) (rightLength : block.2.1.length=layout.inputLog)
    (entries : List (GKRSourceLane × Poly K)) (constants : List (Nat × K))
    (checks : gkrEvaluatedVerifierPath (raw rows) layers [] (rounds++[layout.inputLog]) (earlier++[block])) :
    let h := rows++gkrBlockCoordinates block
    let inputs := gkrRecoveredCircuitInput layout.commonLog entries (gkrHistoryRowpoints layout h) constants
    gkrTerminalMismatch (gkrBindCircuitValues (raw rows) inputs layers) (gkrReverseCircuitValues inputs layers)
      1 [] (rounds++[layout.inputLog]) (earlier++[block]) ↔
      gkrHistoryTerminalClaim layout raw earlier h≠gkrInputFunctional layout.inputLog
        (gkrHistoryLeft layout h) (gkrHistoryRight layout h) (gkrHistoryGamma layout h) inputs := by
  dsimp only
  rw [gkr_history_terminal_claim_inverse layout raw earlier rows block rowLength leftLength rightLength]
  exact gkr_evaluated_joint_terminal_event (raw rows) layers rounds earlier [] block layout rows
    rowLength leftLength rightLength entries constants checks

theorem gkr_history_strategy_regressions :
    gkrHistoryBlock ⟨2,1,1,2⟩ ([11,13,17,19,23] : List Rat)=([17],[19],23) ∧
    gkrHistoryReindex ⟨2,1,1,2⟩ (fun rows block => (rows,block)) ([11,13,17,19,23] : List Rat)=
      ([11,13],([17],[19],23)) ∧
    gkrHistoryBlock ⟨2,1,1,2⟩ ([11,13,17] : List Rat)=([17],[],0) := by decide +kernel

end NearCompression
