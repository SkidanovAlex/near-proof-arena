import NearCompression.TerminalSignedExpansion
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- Expansion through linear arithmetic and multiplication by public constants.
Retained registers are opaque leaves; nonlinear multiplication is not expanded. -/
inductive TerminalWeightedExpansion (nodes : Nat → TerminalDAGNode K) :
    Nat → K → List (Nat × K) → Prop where
  | leaf (i scale) : TerminalWeightedExpansion nodes i scale [(i,scale)]
  | add {i a b scale left right} : nodes i=.binary .add a b →
      TerminalWeightedExpansion nodes a scale left →
      TerminalWeightedExpansion nodes b scale right →
      TerminalWeightedExpansion nodes i scale (left++right)
  | sub {i a b scale left right} : nodes i=.binary .sub a b →
      TerminalWeightedExpansion nodes a scale left →
      TerminalWeightedExpansion nodes b (-scale) right →
      TerminalWeightedExpansion nodes i scale (left++right)
  | scaleLeft {i a b scale c terms} : nodes i=.binary .mul a b → nodes a=.constant c →
      TerminalWeightedExpansion nodes b (scale*c) terms →
      TerminalWeightedExpansion nodes i scale terms
  | scaleRight {i a b scale c terms} : nodes i=.binary .mul a b → nodes b=.constant c →
      TerminalWeightedExpansion nodes a (scale*c) terms →
      TerminalWeightedExpansion nodes i scale terms

def terminalWeightedSum (values : Nat → K) (terms : List (Nat × K)) : K :=
  (terms.map (fun t => t.2*values t.1)).sum

private theorem weighted_sum_append (a b : List K) : (a++b).sum=a.sum+b.sum := by
  induction a with
  | nil => simp; grind
  | cons x xs ih => simp only [List.cons_append,List.sum_cons,ih]; grind

theorem terminal_weighted_expansion_value (inputs values : Nat → K) (nodes : Nat → TerminalDAGNode K)
    (equations : ∀ i, values i=terminalNodeValue inputs values (nodes i))
    (i : Nat) (scale : K) (terms : List (Nat × K))
    (expansion : TerminalWeightedExpansion nodes i scale terms) :
    terminalWeightedSum values terms=scale*values i := by
  induction expansion with
  | leaf i scale => simp [terminalWeightedSum]; grind
  | @add i a b scale left right node ea eb ha hb =>
    have eq := equations i
    rw [node] at eq
    change values i=values a+values b at eq
    unfold terminalWeightedSum at ha hb ⊢
    rw [List.map_append,weighted_sum_append,ha,hb,eq]
    grind
  | @sub i a b scale left right node ea eb ha hb =>
    have eq := equations i
    rw [node] at eq
    change values i=values a-values b at eq
    unfold terminalWeightedSum at ha hb ⊢
    rw [List.map_append,weighted_sum_append,ha,hb,eq]
    grind
  | @scaleLeft i a b scale c terms node constant expansion ih =>
    have eq := equations i
    have hc := equations a
    rw [node] at eq
    rw [constant] at hc
    change values i=values a*values b at eq
    change values a=c at hc
    rw [ih,eq,hc]
    grind
  | @scaleRight i a b scale c terms node constant expansion ih =>
    have eq := equations i
    have hc := equations b
    rw [node] at eq
    rw [constant] at hc
    change values i=values a*values b at eq
    change values b=c at hc
    rw [ih,eq,hc]
    grind

theorem terminal_weighted_expansion_transport
    (inputs sourceValues targetValues : Nat → K) (nodes : Nat → TerminalDAGNode K)
    (equations : ∀ i, sourceValues i=terminalNodeValue inputs sourceValues (nodes i))
    (i : Nat) (scale : K) (terms : List (Nat × K)) (mapping : Nat → Nat)
    (expansion : TerminalWeightedExpansion nodes i scale terms)
    (atoms : ∀ t ∈ terms, targetValues (mapping t.1)=sourceValues t.1) :
    terminalWeightedSum targetValues (terms.map (fun t => (mapping t.1,t.2))) =
      scale*sourceValues i := by
  rw [← terminal_weighted_expansion_value inputs sourceValues nodes equations i scale terms expansion]
  unfold terminalWeightedSum
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply]
  rw [atoms t ht]
theorem terminal_weighted_expansion_executed (inputs : Nat → K) (nodes : List (TerminalDAGNode K))
    (acyclic : TerminalDAGAcyclic 0 nodes) (i : Nat) (scale : K) (terms : List (Nat × K))
    (expansion : TerminalWeightedExpansion (fun j => nodes.getD j (.constant 0)) i scale terms) :
    terminalWeightedSum (terminalDAGRun inputs 0 (fun _ => 0) nodes) terms =
      scale * terminalDAGRun inputs 0 (fun _ => 0) nodes i :=
  terminal_weighted_expansion_value inputs _ _
    (terminal_dag_total_equations inputs nodes acyclic) i scale terms expansion
end NearCompression
