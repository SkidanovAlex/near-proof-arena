import NearCompression.GKRLayerTransition

namespace NearCompression
open Lean.Grind

inductive SwirlGateOp where
  | add | sub | mul

def swirlGateValue {K : Type} [Field K] (op : SwirlGateOp) (a b : K) : K :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b

def swirlWiringSum {K : Type} [Field K]
    (ts : List (SwirlGateOp × K)) (a b : K) : K :=
  match ts with
  | [] => 0
  | (op, w) :: rest => w * swirlGateValue op a b + swirlWiringSum rest a b

def swirlWiringCoefficients {K : Type} [Field K]
    (ts : List (SwirlGateOp × K)) : K × K × K :=
  match ts with
  | [] => (0, 0, 0)
  | (op, w) :: rest =>
    let (x, y, z) := swirlWiringCoefficients rest
    match op with
    | .add => (w + x, y, z)
    | .sub => (x, w + y, z)
    | .mul => (x, y, w + z)

/-- Grouping fixed wiring by operation preserves its evaluation. The weights
must still be derived from the authenticated GKR points and circuit wiring. -/
theorem swirl_grouped_wiring {K : Type} [Field K]
    (ts : List (SwirlGateOp × K)) (a b : K) :
    swirlWiringSum ts a b =
      (swirlWiringCoefficients ts).1 * (a + b) +
      (swirlWiringCoefficients ts).2.1 * (a - b) +
      (swirlWiringCoefficients ts).2.2 * (a * b) := by
  induction ts with
  | nil => simp [swirlWiringSum, swirlWiringCoefficients] <;> grind
  | cons t rest ih =>
    obtain ⟨op, w⟩ := t
    cases op <;>
      simp [swirlWiringSum, swirlWiringCoefficients, swirlGateValue, ih] <;> grind

/-- The emitted endpoint residual is the quadratic sumcheck endpoint test. -/
theorem swirl_quadratic_endpoint {K : Type} [Field K]
    (c₀ c₁ c₂ claim : K) :
    (c₀ + c₀ + (c₁ + c₂)) - claim = 0 ↔
      (c₀ + (0 : K) * (c₁ + 0 * c₂)) +
      (c₀ + (1 : K) * (c₁ + 1 * c₂)) = claim := by
  grind

end NearCompression
