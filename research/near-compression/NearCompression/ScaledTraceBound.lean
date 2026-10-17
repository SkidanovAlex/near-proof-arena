import NearCompression.SwirlGkrVerifierArithmetic
namespace NearCompression

def traceWeightedPair : List (Nat × Nat × Nat) → Nat × Nat
  | [] => (0, 0)
  | (a, b, h) :: rest =>
      let tail := traceWeightedPair rest
      (a * h + tail.1, b * h + tail.2)

/-- Nonnegative trace heights preserve coefficientwise scaled domination. -/
theorem trace_weighted_domination (xs : List (Nat × Nat × Nat)) (scale : Nat)
    (bound : ∀ t ∈ xs, t.1 ≤ scale * t.2.1) :
    (traceWeightedPair xs).1 ≤ scale * (traceWeightedPair xs).2 := by
  induction xs with
  | nil => simp [traceWeightedPair]
  | cons t rest ih =>
    obtain ⟨a, b, h⟩ := t
    have head := Nat.mul_le_mul_right h (bound (a,b,h) (by simp))
    have tail := ih (fun t ht => bound t (by simp [ht]))
    simp only [traceWeightedPair, Nat.mul_add]
    simp only [Nat.mul_assoc] at head
    omega

/-- The positive integer scaling rule used by the native trace-height gate.
The caller must establish the dot-product comparison for nonnegative heights. -/
theorem scaled_trace_bound (actual enforced scale target budget : Nat)
    (positive : 0 < scale) (dominated : actual ≤ scale * enforced)
    (checked : enforced < budget) (fits : scale * budget ≤ target) :
    actual < target := by
  have strict : scale * enforced < scale * budget := Nat.mul_lt_mul_of_pos_left checked positive
  omega

#print axioms scaled_trace_bound
#print axioms trace_weighted_domination
end NearCompression
