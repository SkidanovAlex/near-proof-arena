import NearCompression.GenericRSPairRepresentation
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

def derivedFoldValue (x r : K) (previous : K × K) : K :=
  let eo := rsPairDecode x previous
  eo.1 + r * (eo.2 - eo.1)

def foldPairSelected (side : Bool) (pair : K × K) : K :=
  if side then pair.2 else pair.1

def foldPairRestore (side : Bool) (known other : K) : K × K :=
  if side then (other,known) else (known,other)

theorem derived_fold_affine_value (x r : K) (previous : K × K) :
    derivedFoldValue x r previous =
      (1-r) * (rsPairDecode x previous).1 + r * (rsPairDecode x previous).2 := by
  unfold derivedFoldValue
  grind

omit [Field K] in
theorem fold_pair_restore_exact (side : Bool) (known : K) (pair : K × K)
    (checked : foldPairSelected side pair = known) :
    foldPairRestore side known (foldPairSelected (!side) pair) = pair := by
  rcases pair with ⟨a,b⟩
  cases side <;> simp_all [foldPairSelected,foldPairRestore]

structure FoldTransportStep (K : Type) where
  point : K
  challenge : K
  side : Bool
  child : K × K

def foldTransportConsistent (previous : K × K) : List (FoldTransportStep K) → Prop
  | [] => True
  | step :: rest =>
      foldPairSelected step.side step.child = derivedFoldValue step.point step.challenge previous ∧
      foldTransportConsistent step.child rest

/-- The selected coordinate is discarded and reconstructed at every step.
Only the other coordinate is used from the old child pair. -/
def foldTransportRestore (previous : K × K) : List (FoldTransportStep K) → List (K × K)
  | [] => []
  | step :: rest =>
      let child := foldPairRestore step.side (derivedFoldValue step.point step.challenge previous)
        (foldPairSelected (!step.side) step.child)
      child :: foldTransportRestore child rest

theorem fold_transport_restore_exact (steps : List (FoldTransportStep K))
    (previous : K × K) (checked : foldTransportConsistent previous steps) :
    foldTransportRestore previous steps = steps.map FoldTransportStep.child := by
  induction steps generalizing previous with
  | nil => rfl
  | cons step rest ih =>
    have pair := fold_pair_restore_exact step.side _ step.child checked.1
    simp only [foldTransportRestore, pair, List.map_cons]
    exact congrArg (List.cons step.child) (ih step.child checked.2)

/-- Any authentication/verification predicate over the restored chain sees
exactly the original chain. This makes no hash-binding or soundness claim. -/
theorem fold_transport_preserves_checks (steps : List (FoldTransportStep K))
    (previous : K × K) (checked : foldTransportConsistent previous steps)
    (accepts : List (K × K) → Prop) :
    accepts (foldTransportRestore previous steps) ↔ accepts (steps.map FoldTransportStep.child) := by
  rw [fold_transport_restore_exact steps previous checked]
end NearCompression
