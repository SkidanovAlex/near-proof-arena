import NearCompression.SwirlGkrVerifierArithmetic

namespace NearCompression
open Lean.Grind

def swirlEqDense {K : Type} [Field K] : List K → List K → List K
  | [], xs => xs
  | r :: rs, xs => swirlEqDense rs
      (xs.map (fun x => x * (1 - r)) ++ xs.map (fun x => x * r))

def swirlEqShared {K : Type} [Field K] : List K → List K → List K
  | [], xs => xs
  | r :: rs, xs => swirlEqShared rs
      (xs.map (fun x => x - x * r) ++ xs.map (fun x => x * r))

/-- The low child reuses the high child's product, at arbitrary field points. -/
theorem swirl_eq_shared_child {K : Type} [Field K] (x r : K) :
    x - x * r = x * (1 - r) := by grind

/-- All equality-table coordinates are preserved in their original order.
This is the algorithmic identity, not a Python compiler refinement theorem. -/
theorem swirl_eq_shared_table {K : Type} [Field K] (rs xs : List K) :
    swirlEqShared rs xs = swirlEqDense rs xs := by
  induction rs generalizing xs with
  | nil => rfl
  | cons r rs ih =>
    simp only [swirlEqShared, swirlEqDense, ih, swirl_eq_shared_child]

#print axioms swirl_eq_shared_table
end NearCompression
