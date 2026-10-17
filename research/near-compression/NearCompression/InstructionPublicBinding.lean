import NearCompression.InstructionSumcheckRows

/-! Public six-limb binding for the direct instruction experiment. These prove
algebraic/semantic implications, not random-challenge or cryptographic soundness. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.Wasm

/-- Six limbs encode the two operands and the result in that order. -/
def instructionPublicLimbHolds (row pub : Nat → Fp) : Prop :=
  ∀ c, c < 6 → row c - pub c = 0

theorem instruction_public_limb_eq (row pub : Nat → Fp)
    (h : instructionPublicLimbHolds row pub) (c : Nat) (hc : c < 6) :
    row c = pub c := by
  have hz := h c hc
  grind

theorem instruction_public_word_eq (row pub : Nat → Fp)
    (h : instructionPublicLimbHolds row pub) (lo hi : Nat)
    (hl : lo < 6) (hh : hi < 6) :
    instructionAddWord row lo hi = instructionAddWord pub lo hi := by
  simp only [instructionAddWord, instruction_public_limb_eq row pub h lo hl,
    instruction_public_limb_eq row pub h hi hh]

/-- Publicly claimed operands and result obey the actual Wasm numeric semantics
when the local AIR and the six binding residuals vanish. -/
theorem instruction_public_add_binop (row pub : Nat → Fp)
    (holds : instructionAdd32RangeHolds row)
    (bound : instructionPublicLimbHolds row pub) :
    Num.binop 32 0 (instructionAddWord pub 0 1) (instructionAddWord pub 2 3) =
      some (instructionAddWord pub 4 5) := by
  have h := instruction_add32_range_binop row holds
  rw [instruction_public_word_eq row pub bound 0 1 (by decide) (by decide),
    instruction_public_word_eq row pub bound 2 3 (by decide) (by decide),
    instruction_public_word_eq row pub bound 4 5 (by decide) (by decide)] at h
  exact h

/-- Binding every source row binds each column's multilinear extension at every
point, including the final off-cube sumcheck point. -/
theorem instruction_public_mle_eq (rows pub : Nat → Nat → Fp)
    (bound : ∀ r, r < 8 → instructionPublicLimbHolds (rows r) (pub r))
    (x : InstructionPoint3) (c : Nat) (hc : c < 6) :
    instructionRowsMLE rows x c = instructionRowsMLE pub x c := by
  have h (r : Nat) (hr : r < 8) : rows r c = pub r c :=
    instruction_public_limb_eq _ _ (bound r hr) c hc
  simp only [instructionRowsMLE, h 0 (by decide), h 1 (by decide), h 2 (by decide),
    h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

def instructionPublicBindingPolynomial (rows pub : Nat → Nat → Fp)
    (weights : Nat → Fp) (x : InstructionPoint3) : Fp :=
  ((List.range 6).map (fun c => weights c *
    (instructionRowsMLE rows x c - instructionRowsMLE pub x c))).foldr (·+·) 0

theorem instruction_public_binding_zero (rows pub : Nat → Nat → Fp)
    (bound : ∀ r, r < 8 → instructionPublicLimbHolds (rows r) (pub r))
    (weights : Nat → Fp) (x : InstructionPoint3) :
    instructionPublicBindingPolynomial rows pub weights x = 0 := by
  apply instruction_sum_map_zero
  intro c hc
  rw [instruction_public_mle_eq rows pub bound x c (List.mem_range.mp hc)]
  grind

/-- Adding public residuals preserves the honest Boolean-cube zero target.
Constraint and public batching weights are arbitrary here. -/
theorem instruction_public_sumcheck_zero (rows pub : Nat → Nat → Fp)
    (holds : ∀ r, r < 8 → instructionAdd32RangeHolds (rows r))
    (bound : ∀ r, r < 8 → instructionPublicLimbHolds (rows r) (pub r))
    (weights publicWeights : Nat → Fp) (z : InstructionPoint3) :
    (instructionCube3.map (fun b => instructionAddSumcheckPolynomial rows weights z
      (instructionCubePoint b) + instructionEqPoint z (instructionCubePoint b) *
      instructionPublicBindingPolynomial rows pub publicWeights (instructionCubePoint b))).foldr (·+·) 0 = 0 := by
  apply instruction_sum_map_zero
  intro b hb
  rw [instruction_public_binding_zero rows pub bound publicWeights,
    instruction_sumcheck_boolean_value,
    instruction_constraint_batch_zero weights _ _ (holds _ (instruction_cube_index_bound b)) 0]
  grind

end NearCompression
