import NearCompression.HistoryBranchBudget
namespace NearCompression
open ArenaCore.Security

/-- Disjoint selected-table histories cannot each occupy the whole sample. -/
theorem selected_history_counts_le_length {A : Type} (earlier : List A)
    (branch : A → Option Bool) :
    count earlier (fun a=>branch a=some false)+count earlier (fun a=>branch a=some true)≤earlier.length := by
  classical
  induction earlier with
  | nil => simp [count]
  | cons a rest ih =>
    simp only [count_cons,List.length_cons]
    cases h : branch a with
    | none => simp;omega
    | some b => cases b <;> simp <;> omega

/-- After exact chronological count normalization, the two disjoint local
contributions are bounded by one maximum, not two full-history budgets.
This does not replace the separate bus error term by a maximum. -/
theorem selected_history_weighted_budget {A : Type} (earlier : List A)
    (branch : A → Option Bool) (first second : Nat) :
    count earlier (fun a=>branch a=some false)*first+
      count earlier (fun a=>branch a=some true)*second≤earlier.length*max first second := by
  have bounds := Nat.add_le_add
    (Nat.mul_le_mul_left (count earlier (fun a=>branch a=some false)) (Nat.le_max_left first second))
    (Nat.mul_le_mul_left (count earlier (fun a=>branch a=some true)) (Nat.le_max_right first second))
  rw [←Nat.add_mul] at bounds
  exact Nat.le_trans bounds (Nat.mul_le_mul_right (max first second) (selected_history_counts_le_length earlier branch))

end NearCompression
