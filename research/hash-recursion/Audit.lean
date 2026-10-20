import HashRecursion

-- Run with `lake env lean Audit.lean`. Inspect the dependency closure of every
-- public theorem; no sorryAx, custom axiom or native_decide trust is expected.
#print axioms HashRecursion.existential_wrapper_counterexample
#print axioms HashRecursion.perfect_composition
#print axioms HashRecursion.extraction_event_inclusion
#print axioms HashRecursion.Resources.within_trans
#print axioms HashRecursion.meets_add
#print axioms HashRecursion.cubic_budget
#print axioms HashRecursion.reduction_budget
#print axioms HashRecursion.meets_amplify
#print axioms HashRecursion.meets_sum
#print axioms HashRecursion.cubic_512_at_128
#print axioms HashRecursion.cubic_384_at_64
#print axioms HashRecursion.cubic_384_not_128_at_128
#print axioms HashRecursion.two_full_budgets_fail
#print axioms HashRecursion.serialize_length
#print axioms HashRecursion.paths_216_depth22_512
#print axioms HashRecursion.unshared_paths_exceed_target
#print axioms HashRecursion.paths_128_depth22_512
#print axioms HashRecursion.remaining_budget_128

#print axioms HashRecursion.Quantum.FiniteBasis.involution_perm
#print axioms HashRecursion.Quantum.oracleStep_involution
#print axioms HashRecursion.Quantum.query_involution
#print axioms HashRecursion.Quantum.query_linear
#print axioms HashRecursion.Quantum.query_preserves_pairSum
#print axioms HashRecursion.Quantum.queryDensity_involution
#print axioms HashRecursion.Quantum.queryDensity_pure
#print axioms HashRecursion.Quantum.queryDensity_trace
#print axioms HashRecursion.Quantum.dephaseInput_diagonal
#print axioms HashRecursion.Quantum.recording_is_not_query
#print axioms HashRecursion.Quantum.eventMass_mono
#print axioms HashRecursion.Quantum.eventMass_union_le
#print axioms HashRecursion.Quantum.eventMass_le_total
#print axioms HashRecursion.Quantum.extraction_mass_bound
#print axioms HashRecursion.Quantum.query_preserves_input_event

open HashRecursion

-- Four terms get two bits of slack. These are ERROR NUMERATORS, not a
-- synthesized protocol's security proof. The common denominator is arbitrary.
example (a b c e d : Nat)
    (ha : Meets a d 130) (hb : Meets b d 130)
    (hc : Meets c d 130) (he : Meets e d 130) :
    Meets ([a, b, c, e].sum) d 128 := by
  apply meets_sum (slack := 2) ha.1 (by simp)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc
  · exact he

-- Nonzero constant and two-bit error allocation: 3*128+8+130 = 522.
example : Meets (2 ^ 8 * (2 ^ 128) ^ 3) (2 ^ 522) 130 :=
  cubic_budget 8 128 522 130 (by decide)

-- Strict boundary checks for the illustrative path-only layout.
example : pathBytes 128 22 64 + 119775 < 300000 := by decide
example : ¬ (pathBytes 128 22 64 + 119776 < 300000) := by decide
