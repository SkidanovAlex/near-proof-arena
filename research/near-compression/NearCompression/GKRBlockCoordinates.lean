import NearCompression.ChronologicalChallengeCount
import NearCompression.GKRHistoryCoordinates
import NearCompression.GKRPathCount
namespace NearCompression
open Lean.Grind ArenaCore.Security

/-- Coordinate order used by the PCS joint history: left axis, right axis,
then the fresh gamma challenge. -/
def gkrBlockCoordinates {K : Type} (block : GKRBlock K) : List K :=
  block.1++block.2.1++[block.2.2]

/-- Exact list identity preserves multiplicities even for repeated sample
values. This does not assert Fiat-Shamir challenges are ideal uniform draws. -/
theorem gkr_block_coordinates_uniform {K : Type} (sample : List K) (m : Nat) :
    (gkrChallengeBlocks sample m).map gkrBlockCoordinates=uniformTuples sample (2*m+1) := by
  rw [show 2*m+1=m+(m+1) by omega,uniform_tuples_append sample m (m+1),uniform_tuples_append sample m 1]
  simp only [gkrChallengeBlocks,List.map_flatMap,List.map_map,uniformTuples,List.map_nil,List.map_cons]
  simp only [List.map_eq_flatMap,Function.comp_def,gkrBlockCoordinates,List.append_assoc]

theorem gkr_challenge_paths_append {K : Type} (sample : List K) (first rest : List Nat) :
    gkrChallengePaths sample (first++rest)=
      (gkrChallengePaths sample first).flatMap (fun a => (gkrChallengePaths sample rest).map (fun b => a++b)) := by
  induction first with
  | nil => simp [gkrChallengePaths]
  | cons m first ih =>
    simp only [List.cons_append,gkrChallengePaths,ih,List.flatMap_assoc,List.flatMap_map,List.map_flatMap,List.map_map]
    rfl

/-- The rowpoint prefix and final GKR block enumerate exactly the history
space used by the merged near/far PCS bound. Rows remain sampled here. -/
theorem gkr_rows_final_block_history {K : Type} (sample : List K) (layout : GKRJointLayout) :
    (uniformTuples sample layout.rowCoordinates).flatMap (fun rows =>
      (gkrChallengeBlocks sample layout.inputLog).map (fun block => rows++gkrBlockCoordinates block))=
    uniformTuples sample (gkrHistoryLength layout) := by
  change _=uniformTuples sample (layout.rowCoordinates+(2*layout.inputLog+1))
  rw [uniform_tuples_append]
  congr 1
  funext rows
  rw [←gkr_block_coordinates_uniform sample layout.inputLog,List.map_map]
  rfl

/-- Adding the weighted-PCS opening point gives the complete outer joint
space, in the same order as gkr_joint_failure_acceptance_count. -/
theorem gkr_rows_block_pcs_coordinates {K : Type} (sample : List K) (layout : GKRJointLayout) :
    (uniformTuples sample layout.rowCoordinates).flatMap (fun rows =>
      (gkrChallengeBlocks sample layout.inputLog).flatMap (fun block =>
        (uniformTuples sample layout.commonLog).map (fun z => (rows++gkrBlockCoordinates block)++z)))=
    uniformTuples sample (heterogeneousJointDimension layout) := by
  change _=uniformTuples sample (gkrHistoryLength layout+layout.commonLog)
  rw [uniform_tuples_append,←gkr_rows_final_block_history]
  simp only [List.flatMap_assoc,List.flatMap_map]

/-- Any predicate, including accepted mismatch with continuation queries,
has the same count after the concrete coordinate assembly. -/
theorem gkr_rows_block_pcs_event_count {K R : Type} (sample : List K) (layout : GKRJointLayout)
    (continuations : List R) (event : List K → R → Prop) :
    count ((uniformTuples sample layout.rowCoordinates).flatMap (fun rows =>
      (gkrChallengeBlocks sample layout.inputLog).flatMap (fun block =>
        (uniformTuples sample layout.commonLog).flatMap (fun z =>
          continuations.map (fun r => ((rows++gkrBlockCoordinates block)++z,r))))))
      (fun pair => event pair.1 pair.2)=
    count ((uniformTuples sample (heterogeneousJointDimension layout)).flatMap
      (fun z => continuations.map (fun r => (z,r)))) (fun pair => event pair.1 pair.2) := by
  rw [←gkr_rows_block_pcs_coordinates sample layout]
  simp only [List.flatMap_assoc,List.flatMap_map]

/-- Axis order and multiplicities are observable, including a zero-axis
block. Duplicate challenge values are not silently deduplicated. -/
theorem gkr_block_coordinate_regressions :
    gkrBlockCoordinates (([2],[3],5) : GKRBlock Nat)=[2,3,5] ∧
    gkrBlockCoordinates (([],[],7) : GKRBlock Nat)=[7] ∧
    (gkrChallengeBlocks ([0,0] : List Nat) 1).length=8 ∧
    ((gkrChallengeBlocks ([0,0] : List Nat) 1).map gkrBlockCoordinates)=List.replicate 8 [0,0,0] ∧
    ((gkrChallengeBlocks ([0,1] : List Nat) 1).map gkrBlockCoordinates).head?=some [0,0,0] := by decide +kernel

end NearCompression
