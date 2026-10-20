import NearCompression.TerminalDAGBalance
import NearCompression.TerminalWeightedAggregation
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- A heap may reorder its frontier arbitrarily, then replace two registers by
an emitted sum. Depth priorities affect cost, not the algebraic invariant. -/
inductive TerminalHeapRoute (nodes : Nat → TerminalDAGNode K) : List Nat → Nat → Prop where
  | empty {z} : nodes z = .constant 0 → TerminalHeapRoute nodes [] z
  | singleton (x) : TerminalHeapRoute nodes [x] x
  | merge {a b c rest z} : TerminalArithmeticRoute nodes .add a b c →
      TerminalHeapRoute nodes (c :: rest) z → TerminalHeapRoute nodes (a :: b :: rest) z
  | reorder {before after z} : before.Perm after →
      TerminalHeapRoute nodes after z → TerminalHeapRoute nodes before z

private theorem register_sum_permutation (values : Nat → K) (left right : List Nat)
    (permutation : left.Perm right) : (left.map values).sum = (right.map values).sum := by
  induction permutation with
  | nil => rfl
  | cons t h ih => simp only [List.map_cons, List.sum_cons, ih]
  | swap a b rest => simp only [List.map_cons, List.sum_cons]; grind
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem terminal_heap_route_value (inputs values : Nat → K) (nodes : Nat → TerminalDAGNode K)
    (equations : ∀ i, values i = terminalNodeValue inputs values (nodes i))
    (terms : List Nat) (z : Nat) (route : TerminalHeapRoute nodes terms z) :
    values z = (terms.map values).sum := by
  induction route with
  | @empty z node =>
    have h := equations z
    simpa only [node, terminalNodeValue, List.map_nil, List.sum_nil] using h
  | singleton x => simp; grind
  | @merge a b c rest z join route ih =>
    have eq := terminal_arithmetic_route_value nodes inputs values equations _ _ _ _ join
    simp only [gkrGateValue] at eq
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, eq]
    grind
  | @reorder before after z permutation route ih =>
    rw [ih, register_sum_permutation values before after permutation]

/-- Weighted leaves can be justified by the same arithmetic routes that cover
public constant folding and multiplication by zero or one. -/
theorem terminal_weighted_leaf_route
    (inputs values : Nat → K) (nodes : Nat → TerminalDAGNode K)
    (equations : ∀ i, values i = terminalNodeValue inputs values (nodes i))
    (constant atom output : Nat) (weight value : K)
    (literal : nodes constant = .constant weight)
    (retained : values atom = value)
    (route : TerminalArithmeticRoute nodes .mul constant atom output) :
    values output = weight * value := by
  have result := terminal_arithmetic_route_value nodes inputs values equations _ _ _ _ route
  have hc := equations constant
  simp only [literal, terminalNodeValue] at hc
  simpa only [gkrGateValue, hc, retained] using result

/-- Composition boundary for weighted collection, coefficient aggregation,
permutation, weighted-leaf emission, and arbitrary heap merges. The emitter
must still establish its leaf equations and the concrete heap route. -/
theorem terminal_weighted_heap_rebuild [DecidableEq K]
    (sourceInputs sourceValues targetInputs targetValues : Nat → K)
    (sourceNodes targetNodes : Nat → TerminalDAGNode K)
    (sourceEquations : ∀ i, sourceValues i = terminalNodeValue sourceInputs sourceValues (sourceNodes i))
    (targetEquations : ∀ i, targetValues i = terminalNodeValue targetInputs targetValues (targetNodes i))
    (root z : Nat) (terms reordered : List (Nat × K)) (emit : Nat × K → Nat)
    (expansion : TerminalWeightedExpansion sourceNodes root 1 terms)
    (order : ((terminalWeightedAggregate terms).filter (fun t => decide (t.2 ≠ 0))).Perm reordered)
    (leaves : ∀ t ∈ reordered, targetValues (emit t) = t.2 * sourceValues t.1)
    (route : TerminalHeapRoute targetNodes (reordered.map emit) z) :
    targetValues z = sourceValues root := by
  rw [terminal_heap_route_value targetInputs targetValues targetNodes targetEquations _ _ route]
  have leaf_sum : ((reordered.map emit).map targetValues).sum =
      terminalWeightedSum sourceValues reordered := by
    unfold terminalWeightedSum
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact leaves t ht
  rw [leaf_sum, ← terminal_weighted_permutation_value sourceValues _ _ order,
      terminal_weighted_zero_drop, terminal_weighted_aggregate_value,
      terminal_weighted_expansion_value sourceInputs sourceValues sourceNodes sourceEquations _ _ _ expansion]
  grind
end NearCompression
