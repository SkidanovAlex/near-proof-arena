import NearCompression.GKRLayerTransition

namespace NearCompression
open Lean.Grind

/-- Slot tags are assigned by the verifier's trusted coordinate map. -/
structure SwirlInputTerm (K : Type) where
  weight : K
  value : K
  known : Bool

variable {K : Type} [Field K]

def swirlInputSum : List (SwirlInputTerm K) → K
  | [] => 0
  | t :: ts => t.weight * t.value + swirlInputSum ts

def swirlKnownInputSum : List (SwirlInputTerm K) → K
  | [] => 0
  | t :: ts => (if t.known then t.weight * t.value else 0) + swirlKnownInputSum ts

def swirlPcsInputSum : List (SwirlInputTerm K) → K
  | [] => 0
  | t :: ts => (if t.known then 0 else t.weight * t.value) + swirlPcsInputSum ts

/-- Exact functional partition. Cryptographic binding and trusted coordinate
provenance remain separate obligations. -/
theorem swirl_input_sum_partition (ts : List (SwirlInputTerm K)) :
    swirlInputSum ts = swirlKnownInputSum ts + swirlPcsInputSum ts := by
  induction ts with
  | nil => simp [swirlInputSum, swirlKnownInputSum, swirlPcsInputSum] <;> grind
  | cons t ts ih =>
    cases h : t.known <;>
      simp [swirlInputSum, swirlKnownInputSum, swirlPcsInputSum, h, ih] <;> grind

/-- Subtracting the trusted known contribution leaves exactly the PCS claim. -/
theorem swirl_input_residual_iff (ts : List (SwirlInputTerm K)) (claim : K) :
    swirlInputSum ts = claim ↔
      swirlPcsInputSum ts = claim - swirlKnownInputSum ts := by
  rw [swirl_input_sum_partition]
  constructor <;> intro h <;> grind

end NearCompression
