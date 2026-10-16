import NearCompression.GKRBlockCoordinates
import NearCompression.GKREvaluatedStrategy
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

private theorem block_extract {K : Type} [Field K] (earlier axis suffix : List K) :
    gkrPointBlock earlier.length axis.length (fun i => ((earlier++axis)++suffix).getD i 0)=
      (fun i => axis.getD i 0) := by
  funext i
  unfold gkrPointBlock
  by_cases hi : i<axis.length
  · have hp : earlier.length≤earlier.length+i := by omega
    have ha : earlier.length+i<(earlier++axis).length := by simp;omega
    simp only [hi,ite_true,List.getD,List.getElem?_append_left ha,List.getElem?_append_right hp,
      Nat.add_sub_cancel_left]
  · simp only [hi,ite_false,List.getD,List.getElem?_eq_none (by omega : axis.length≤i),Option.getD_none]

/-- Every axis and gamma accessor recovers its actual final-block value,
including out-of-range axis coordinates, which are zero on both sides. -/
theorem gkr_joint_history_accessors {K : Type} [Field K]
    (layout : GKRJointLayout) (rows : List K) (block : GKRBlock K)
    (rowLength : rows.length=layout.rowCoordinates)
    (leftLength : block.1.length=layout.inputLog) (rightLength : block.2.1.length=layout.inputLog) :
    gkrHistoryLeft layout (rows++gkrBlockCoordinates block)=(fun i => block.1.getD i 0) ∧
    gkrHistoryRight layout (rows++gkrBlockCoordinates block)=(fun i => block.2.1.getD i 0) ∧
    gkrHistoryGamma layout (rows++gkrBlockCoordinates block)=block.2.2 := by
  rcases block with ⟨left,right,gamma⟩
  dsimp only at leftLength rightLength ⊢
  constructor
  · simpa only [gkrHistoryLeft,←rowLength,←leftLength,gkrBlockCoordinates,List.append_assoc] using
      block_extract rows left (right++[gamma])
  constructor
  · have size : (rows++left).length=layout.rowCoordinates+layout.inputLog := by simp [rowLength,leftLength]
    unfold gkrHistoryRight
    rw [←size]
    rw [←rightLength]
    simpa only [gkrBlockCoordinates,List.append_assoc] using block_extract (rows++left) right [gamma]
  · have size : ((rows++left)++right).length=layout.rowCoordinates+2*layout.inputLog := by
      simp [rowLength,leftLength,rightLength];omega
    unfold gkrHistoryGamma gkrBlockCoordinates
    rw [←size]
    simp only [←List.append_assoc,List.getD,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,
      List.getElem?_cons_zero,Option.getD_some]

/-- Appending the final block cannot alter a valid source lane's rowpoint. -/
theorem gkr_joint_history_rows_unchanged {K : Type} [Field K]
    (layout : GKRJointLayout) (rows suffix : List K) (lane : GKRSourceLane)
    (rowLength : rows.length=layout.rowCoordinates)
    (bound : lane.rowOffset+lane.rowLog≤layout.rowCoordinates) :
    gkrHistoryRowpoints layout (rows++suffix) lane=gkrHistoryRowpoints layout rows lane := by
  funext i
  unfold gkrHistoryRowpoints gkrPointBlock
  by_cases hi : i<lane.rowLog
  · simp only [hi,ite_true,List.getD,List.getElem?_append_left (show lane.rowOffset+i<rows.length by omega)]
  · simp only [hi,ite_false]

/-- The take/drop split in the merged PCS event recovers exactly the assembled
history and PCS suffix. Lengths are required, not inferred from padding. -/
theorem gkr_joint_history_suffix_split {K : Type} [Field K]
    (layout : GKRJointLayout) (rows : List K) (block : GKRBlock K) (suffix : List K)
    (rowLength : rows.length=layout.rowCoordinates)
    (leftLength : block.1.length=layout.inputLog) (rightLength : block.2.1.length=layout.inputLog) :
    ((rows++gkrBlockCoordinates block)++suffix).take (gkrHistoryLength layout)=rows++gkrBlockCoordinates block ∧
    ((rows++gkrBlockCoordinates block)++suffix).drop (gkrHistoryLength layout)=suffix := by
  have length : (rows++gkrBlockCoordinates block).length=gkrHistoryLength layout := by
    simp only [gkrBlockCoordinates,List.length_append,List.length_cons,List.length_nil,rowLength,leftLength,rightLength,gkrHistoryLength]
    omega
  rw [←length]
  exact ⟨List.take_append_length,List.drop_append_length⟩

/-- The terminal mismatch from the evaluated GKR path uses exactly the
joint-history input functional, rather than separately supplied coordinates.
The common source tuple and constants are still explicit inputs. -/
theorem gkr_evaluated_joint_terminal_event {K : Type} [Field K]
    (raw : (m : Nat) → List (GKRBlock K) → GKRLayerStrategy K m)
    (layers : List (List GKRWiringGate)) (rounds : List Nat)
    (blocks history : List (GKRBlock K)) (block : GKRBlock K)
    (layout : GKRJointLayout) (rows : List K)
    (rowLength : rows.length=layout.rowCoordinates)
    (leftLength : block.1.length=layout.inputLog) (rightLength : block.2.1.length=layout.inputLog)
    (entries : List (GKRSourceLane × Poly K)) (constants : List (Nat × K))
    (checks : gkrEvaluatedVerifierPath raw layers history (rounds++[layout.inputLog]) (blocks++[block])) :
    let h := rows++gkrBlockCoordinates block
    let inputs := gkrRecoveredCircuitInput layout.commonLog entries (gkrHistoryRowpoints layout h) constants
    gkrTerminalMismatch (gkrBindCircuitValues raw inputs layers) (gkrReverseCircuitValues inputs layers)
      (history.length+1) history (rounds++[layout.inputLog]) (blocks++[block]) ↔
      (raw layout.inputLog (history++blocks)).a block.1 block.2.1+
        block.2.2*(raw layout.inputLog (history++blocks)).b block.1 block.2.1≠
      gkrInputFunctional layout.inputLog (gkrHistoryLeft layout h) (gkrHistoryRight layout h)
        (gkrHistoryGamma layout h) inputs := by
  dsimp only
  have access := gkr_joint_history_accessors layout rows block rowLength leftLength rightLength
  rw [access.1,access.2.1,access.2.2]
  exact gkr_evaluated_path_recovered_mismatch raw layers rounds blocks history block layout entries _ constants checks

theorem gkr_joint_accessor_regressions :
    gkrHistoryLeft ⟨2,1,1,2⟩ ([11,13,17,19,23] : List Rat) 0=17 ∧
    gkrHistoryRight ⟨2,1,1,2⟩ ([11,13,17,19,23] : List Rat) 0=19 ∧
    gkrHistoryGamma ⟨2,1,1,2⟩ ([11,13,17,19,23] : List Rat)=23 ∧
    gkrHistoryLeft ⟨2,1,1,2⟩ ([11,13,17,19,23] : List Rat) 1=0 ∧
    gkrHistoryGamma ⟨1,1,1,2⟩ ([11,13,17,19,23] : List Rat)=19 := by decide +kernel

end NearCompression
