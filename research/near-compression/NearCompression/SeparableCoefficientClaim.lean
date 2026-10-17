import NearCompression.TerminalWeightedExpansion
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- Each row consists of a source coefficient and its two row weights. Moving
column weights outside the row sum avoids materializing the tensor. -/
theorem separable_coefficient_claim (a b : K) (rows : List (K × K × K)) :
    (rows.map (fun row => row.1 * (a * row.2.1 + b * row.2.2))).sum =
      a * (rows.map (fun row => row.1 * row.2.1)).sum +
      b * (rows.map (fun row => row.1 * row.2.2)).sum := by
  induction rows with
  | nil => simp; grind
  | cons row rows ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    grind
end NearCompression
