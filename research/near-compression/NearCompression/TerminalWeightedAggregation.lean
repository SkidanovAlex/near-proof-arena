import NearCompression.TerminalWeightedExpansion
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- Reference association-list insertion combines weights at equal registers. -/
def terminalWeightedInsert (term : Nat × K) : List (Nat × K) → List (Nat × K)
  | [] => [term]
  | t :: ts => if term.1 = t.1 then (t.1, term.2 + t.2) :: ts
      else t :: terminalWeightedInsert term ts

theorem terminal_weighted_insert_value (values : Nat → K) (term : Nat × K)
    (terms : List (Nat × K)) :
    terminalWeightedSum values (terminalWeightedInsert term terms) =
      term.2 * values term.1 + terminalWeightedSum values terms := by
  induction terms with
  | nil => simp [terminalWeightedInsert, terminalWeightedSum]
  | cons t ts ih =>
    simp only [terminalWeightedInsert]
    split
    next h =>
      simp only [terminalWeightedSum, List.map_cons, List.sum_cons]
      rw [h]
      grind
    next h =>
      change t.2 * values t.1 + terminalWeightedSum values (terminalWeightedInsert term ts) =
        term.2 * values term.1 + (t.2 * values t.1 + terminalWeightedSum values ts)
      rw [ih]
      grind

def terminalWeightedAggregate (terms : List (Nat × K)) : List (Nat × K) :=
  terms.foldr terminalWeightedInsert []

theorem terminal_weighted_aggregate_value (values : Nat → K) (terms : List (Nat × K)) :
    terminalWeightedSum values (terminalWeightedAggregate terms) =
      terminalWeightedSum values terms := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    change terminalWeightedSum values (terminalWeightedInsert t (terminalWeightedAggregate ts)) = _
    rw [terminal_weighted_insert_value, ih]
    rfl

theorem terminal_weighted_zero_drop [DecidableEq K] (values : Nat → K) (terms : List (Nat × K)) :
    terminalWeightedSum values (terms.filter (fun t => decide (t.2 ≠ 0))) =
      terminalWeightedSum values terms := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    by_cases h : t.2 = 0
    · simp [h, terminalWeightedSum] at *
      grind
    · simp [h, terminalWeightedSum] at *
      grind
theorem terminal_weighted_permutation_value (values : Nat → K)
    (left right : List (Nat × K)) (permutation : left.Perm right) :
    terminalWeightedSum values left = terminalWeightedSum values right := by
  induction permutation with
  | nil => rfl
  | cons t h ih =>
    change t.2 * values t.1 + terminalWeightedSum values _ =
      t.2 * values t.1 + terminalWeightedSum values _
    rw [ih]
  | swap a b rest =>
    simp only [terminalWeightedSum, List.map_cons, List.sum_cons]
    grind
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
end NearCompression
