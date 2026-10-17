import NearCompression.GKRLayerTransition

namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- A fixed linear summary loses information needed by a multiplication gate.
This is a deterministic interface obstruction, not an attack on a protocol
which fixes the witness before sampling a fresh batching challenge. -/
theorem swirl_linear_summary_collision (r : K) (hr : r ≠ 0) :
    (0 : K) + r * 0 = r + r * (-1) ∧
      (0 : K) * 0 ≠ r * (-1) := by
  constructor
  · grind
  · grind

/-- Therefore replacing disclosed columns with only their linear summary
cannot preserve direct evaluation of even one multiplication gate. A valid
replacement needs an additional argument connecting the nonlinear evaluation
and the PCS claim to the same committed input. -/
theorem swirl_product_not_function_of_linear_summary (r : K) (hr : r ≠ 0) :
    ¬ ∃ f : K → K, ∀ x y : K, f (x + r * y) = x * y := by
  rintro ⟨f, hf⟩
  have hzero := hf 0 0
  have hother := hf r (-1)
  obtain ⟨hsame, hdiff⟩ := swirl_linear_summary_collision r hr
  rw [hsame] at hzero
  exact hdiff (hzero.symm.trans hother)

end NearCompression
