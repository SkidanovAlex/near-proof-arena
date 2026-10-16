import NearCompression.TerminalDAGEvaluation
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

theorem terminal_dag_preserves_later (inputs previous : Nat → K)
    (nodes : List (TerminalDAGNode K)) (index i : Nat) (later : index+nodes.length≤i) :
    terminalDAGRun inputs index previous nodes i=previous i := by
  induction nodes generalizing index previous with
  | nil => rfl
  | cons node rest ih =>
    rw [terminalDAGRun,ih _ _ (by simp only [List.length_cons] at later; omega)]
    simp [terminalStore,show i≠index by simp only [List.length_cons] at later; omega]

/-- Default zero nodes agree with untouched zero registers outside the program.
This total interface is derived from execution; it is not an oracle premise. -/
theorem terminal_dag_total_equations (inputs : Nat → K) (nodes : List (TerminalDAGNode K))
    (acyclic : TerminalDAGAcyclic 0 nodes) (i : Nat) :
    terminalDAGRun inputs 0 (fun _ => 0) nodes i=
      terminalNodeValue inputs (terminalDAGRun inputs 0 (fun _ => 0) nodes)
        (nodes.getD i (.constant 0)) := by
  by_cases hi : i<nodes.length
  · have h := terminal_dag_node_equation inputs (fun _ => 0) nodes 0 acyclic i hi
    simpa only [Nat.zero_add,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using h
  · rw [terminal_dag_preserves_later inputs (fun _ => 0) nodes 0 i (by omega)]
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : nodes.length≤i),terminalNodeValue]
end NearCompression
