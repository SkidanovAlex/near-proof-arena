import NearCompression.RecursiveSourceProgram
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Exact seven-node block emitted for one lane: beta is shared by both
products, input order beta/left/right, then mul/add-left and mul/add-right. -/
def recursiveSharedLaneNodes (start slot left right : Nat) : List (TerminalDAGNode K) :=
  [.input slot,.input (slot+1),.input (slot+2),
   .binary .mul start (start+1),.binary .add left (start+3),
   .binary .mul start (start+2),.binary .add right (start+5)]

omit [Field K] in
theorem recursive_shared_lane_acyclic (start slot left right : Nat)
    (hl : left<start) (hr : right<start) :
    TerminalDAGAcyclic start (recursiveSharedLaneNodes (K:=K) start slot left right) := by
  simp only [recursiveSharedLaneNodes,TerminalDAGAcyclic,TerminalNodeBefore]
  simp only [true_and,and_true]
  grind

/-- Exact shared-node execution, for arbitrary operands and old accumulator
values. No supplied semantic equations, honest inputs, or route certificate. -/
theorem recursive_shared_lane_value (start slot left right : Nat)
    (inputs previous : Nat → K) (hl : left<start) (hr : right<start) :
    let result:=terminalDAGRun inputs start previous (recursiveSharedLaneNodes start slot left right)
    result (start+4)=previous left+inputs slot*inputs (slot+1) ∧
    result (start+6)=previous right+inputs slot*inputs (slot+2) := by
  dsimp only
  let nodes := recursiveSharedLaneNodes (K:=K) start slot left right
  have acyclic := recursive_shared_lane_acyclic (K:=K) start slot left right hl hr
  have h0 := terminal_dag_node_equation inputs previous nodes start acyclic 0 (by simp [nodes,recursiveSharedLaneNodes])
  have h1 := terminal_dag_node_equation inputs previous nodes start acyclic 1 (by simp [nodes,recursiveSharedLaneNodes])
  have h2 := terminal_dag_node_equation inputs previous nodes start acyclic 2 (by simp [nodes,recursiveSharedLaneNodes])
  have h3 := terminal_dag_node_equation inputs previous nodes start acyclic 3 (by simp [nodes,recursiveSharedLaneNodes])
  have h4 := terminal_dag_node_equation inputs previous nodes start acyclic 4 (by simp [nodes,recursiveSharedLaneNodes])
  have h5 := terminal_dag_node_equation inputs previous nodes start acyclic 5 (by simp [nodes,recursiveSharedLaneNodes])
  have h6 := terminal_dag_node_equation inputs previous nodes start acyclic 6 (by simp [nodes,recursiveSharedLaneNodes])
  have pl := terminal_dag_preserves_earlier inputs previous nodes start left hl
  have pr := terminal_dag_preserves_earlier inputs previous nodes start right hr
  simp only [nodes,recursiveSharedLaneNodes,List.getElem_cons_zero,List.getElem_cons_succ,
    Nat.add_zero,terminalNodeValue,gkrGateValue] at h0 h1 h2 h3 h4 h5 h6
  change terminalDAGRun inputs start previous nodes (start+4)=_ ∧
    terminalDAGRun inputs start previous nodes (start+6)=_
  change terminalDAGRun inputs start previous nodes start=inputs slot at h0
  change terminalDAGRun inputs start previous nodes (start+1)=inputs (slot+1) at h1
  change terminalDAGRun inputs start previous nodes (start+2)=inputs (slot+2) at h2
  change terminalDAGRun inputs start previous nodes (start+3)=terminalDAGRun inputs start previous nodes start*terminalDAGRun inputs start previous nodes (start+1) at h3
  change terminalDAGRun inputs start previous nodes (start+4)=terminalDAGRun inputs start previous nodes left+terminalDAGRun inputs start previous nodes (start+3) at h4
  change terminalDAGRun inputs start previous nodes (start+5)=terminalDAGRun inputs start previous nodes start*terminalDAGRun inputs start previous nodes (start+2) at h5
  change terminalDAGRun inputs start previous nodes (start+6)=terminalDAGRun inputs start previous nodes right+terminalDAGRun inputs start previous nodes (start+5) at h6
  grind


theorem recursive_shared_run_append (inputs previous : Nat → K) (index : Nat)
    (a b : List (TerminalDAGNode K)) :
    terminalDAGRun inputs index previous (a++b)=
      terminalDAGRun inputs (index+a.length) (terminalDAGRun inputs index previous a) b := by
  induction a generalizing index previous with
  | nil => simp only [List.nil_append,List.length_nil,Nat.add_zero,terminalDAGRun]
  | cons node rest ih =>
    simp only [List.cons_append,terminalDAGRun,List.length_cons,ih]
    have hi : index+1+rest.length=index+(rest.length+1) := by omega
    rw [hi]

omit [Field K] in
theorem recursive_shared_acyclic_append (index : Nat) (a b : List (TerminalDAGNode K))
    (ha : TerminalDAGAcyclic index a) (hb : TerminalDAGAcyclic (index+a.length) b) :
    TerminalDAGAcyclic index (a++b) := by
  induction a generalizing index with
  | nil => simpa using hb
  | cons node rest ih =>
    exact ⟨ha.1,ih (index+1) ha.2 (by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hb)⟩

def recursiveSharedLaneProgram (start slot left right : Nat) : Nat → List (TerminalDAGNode K)
  | 0 => []
  | n+1 => recursiveSharedLaneNodes start slot left right ++
      recursiveSharedLaneProgram (start+7) (slot+3) (start+4) (start+6) n

def recursiveSharedLaneIndex (start previous : Nat) (side : Bool) : Nat → Nat
  | 0 => previous
  | n+1 => recursiveSharedLaneIndex (start+7) (start+(if side then 6 else 4)) side n

omit [Field K] in
theorem recursive_shared_lane_program_length (start slot left right n : Nat) :
    (recursiveSharedLaneProgram (K:=K) start slot left right n).length=7*n := by
  induction n generalizing start slot left right with
  | zero => rfl
  | succ n ih =>
    simp only [recursiveSharedLaneProgram,List.length_append,recursiveSharedLaneNodes,List.length_cons,List.length_nil,ih]
    omega

theorem recursive_shared_lane_index_bound (start previous n : Nat) (side : Bool)
    (hp : previous<start) : recursiveSharedLaneIndex start previous side n<start+7*n := by
  induction n generalizing start previous with
  | zero => simpa only [recursiveSharedLaneIndex,Nat.mul_zero,Nat.add_zero] using hp
  | succ n ih =>
    have h := ih (start+7) (start+(if side then 6 else 4)) (by split <;> omega)
    simpa only [recursiveSharedLaneIndex] using (show recursiveSharedLaneIndex (start+7) (start+(if side then 6 else 4)) side n<start+7*(n+1) by omega)

theorem recursive_shared_lane_program_acyclic (start slot left right n : Nat)
    (hl : left<start) (hr : right<start) :
    TerminalDAGAcyclic start (recursiveSharedLaneProgram (K:=K) start slot left right n) := by
  induction n generalizing start slot left right with
  | zero => trivial
  | succ n ih =>
    apply recursive_shared_acyclic_append
    · exact recursive_shared_lane_acyclic start slot left right hl hr
    · simpa only [recursiveSharedLaneNodes,List.length_cons,List.length_nil] using
        ih (start+7) (slot+3) (start+4) (start+6) (by omega) (by omega)

private theorem source_lane_shift (inputs : Nat → K) (slot n : Nat) (side : Bool) (acc : K) :
    recursiveSourceLaneValue inputs slot side acc (n+1)=
      recursiveSourceLaneValue inputs (slot+3) side
        (acc+inputs slot*inputs (slot+(if side then 2 else 1))) n := by
  induction n generalizing slot acc with
  | zero => simp only [recursiveSourceLaneValue,Nat.mul_zero,Nat.add_zero]
  | succ n ih =>
    rw [recursiveSourceLaneValue,ih,recursiveSourceLaneValue]
    have index : slot+3*(n+1)=slot+3+3*n := by omega
    rw [index]

/-- The exact shared emitter lane loop, rather than the expanded tree compiler. -/
theorem recursive_shared_lane_program_value (start slot left right n : Nat)
    (inputs previous : Nat → K) (hl : left<start) (hr : right<start) :
    let result:=terminalDAGRun inputs start previous (recursiveSharedLaneProgram start slot left right n)
    result (recursiveSharedLaneIndex start left false n)=recursiveSourceLaneValue inputs slot false (previous left) n ∧
    result (recursiveSharedLaneIndex start right true n)=recursiveSourceLaneValue inputs slot true (previous right) n := by
  induction n generalizing start slot left right previous with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    dsimp only
    rw [recursiveSharedLaneProgram,recursive_shared_run_append]
    rw [show (recursiveSharedLaneNodes (K:=K) start slot left right).length=7 from rfl]
    have middle := recursive_shared_lane_value start slot left right inputs previous hl hr
    have next := ih (start+7) (slot+3) (start+4) (start+6)
      (terminalDAGRun inputs start previous (recursiveSharedLaneNodes start slot left right)) (by omega) (by omega)
    dsimp only at middle next
    rw [middle.1,middle.2] at next
    simpa only [recursiveSharedLaneIndex,source_lane_shift,Bool.false_eq_true,ite_false,ite_true] using next

end NearCompression
