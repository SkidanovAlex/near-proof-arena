import NearCompression.TerminalDAGTotalSemantics
import NearCompression.TerminalSignedBalance
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- collect(k,sign) may stop at a retained register, or expand add/sub. Uses
counts only choose where to stop; they are not an algebraic premise. -/
inductive TerminalSignedExpansion (nodes : Nat → TerminalDAGNode K) :
    Nat → Bool → List (Nat × Bool) → Prop where
  | leaf (i sign) : TerminalSignedExpansion nodes i sign [(i,sign)]
  | add {i left right sign a b} : nodes i=.binary .add left right →
      TerminalSignedExpansion nodes left sign a → TerminalSignedExpansion nodes right sign b →
      TerminalSignedExpansion nodes i sign (a++b)
  | sub {i left right sign a b} : nodes i=.binary .sub left right →
      TerminalSignedExpansion nodes left sign a → TerminalSignedExpansion nodes right (!sign) b →
      TerminalSignedExpansion nodes i sign (a++b)

def terminalRegisterSignedSum (values : Nat → K) (terms : List (Nat × Bool)) : K :=
  (terms.map (fun t => terminalSignedValue (values t.1,t.2))).sum

private theorem signed_sum_append (a b : List K) : (a++b).sum=a.sum+b.sum := by
  induction a with
  | nil => simp; grind
  | cons x xs ih => simp only [List.cons_append,List.sum_cons,ih]; grind

theorem terminal_signed_expansion_value (inputs values : Nat → K) (nodes : Nat → TerminalDAGNode K)
    (equations : ∀ i,values i=terminalNodeValue inputs values (nodes i))
    (i : Nat) (sign : Bool) (terms : List (Nat × Bool))
    (expansion : TerminalSignedExpansion nodes i sign terms) :
    terminalRegisterSignedSum values terms=terminalSignedValue (values i,sign) := by
  induction expansion with
  | leaf i sign => simp only [terminalRegisterSignedSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]; grind
  | @add i left right sign a b node ea eb ha hb =>
    have eq := equations i
    rw [node] at eq
    change values i=values left+values right at eq
    unfold terminalRegisterSignedSum at ha hb ⊢
    rw [List.map_append,signed_sum_append,ha,hb,eq]
    cases sign <;> simp [terminalSignedValue] <;> grind
  | @sub i left right sign a b node ea eb ha hb =>
    have eq := equations i
    rw [node] at eq
    change values i=values left-values right at eq
    unfold terminalRegisterSignedSum at ha hb ⊢
    rw [List.map_append,signed_sum_append,ha,hb,eq]
    cases sign <;> simp [terminalSignedValue] <;> grind

theorem terminal_signed_expansion_executed (inputs : Nat → K) (nodes : List (TerminalDAGNode K))
    (acyclic : TerminalDAGAcyclic 0 nodes) (i : Nat) (sign : Bool) (terms : List (Nat × Bool))
    (expansion : TerminalSignedExpansion (fun j => nodes.getD j (.constant 0)) i sign terms) :
    terminalRegisterSignedSum (terminalDAGRun inputs 0 (fun _ => 0) nodes) terms=
      terminalSignedValue (terminalDAGRun inputs 0 (fun _ => 0) nodes i,sign) :=
  terminal_signed_expansion_value inputs _ _ (terminal_dag_total_equations inputs nodes acyclic) i sign terms expansion
end NearCompression
