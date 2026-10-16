import NearCompression.InstructionAddTrace
import NearCompression.InstructionAddRange

namespace NearCompression
open NearSpecV3.Wasm ZkFormal.Air ZkFormal.Algebra

theorem instruction_bit_expr_local (base n : Nat) :
    instructionLocalExpr (instructionBitExpr base n) := by
  induction n generalizing base with
  | zero => trivial
  | succ n ih => exact ⟨rfl, trivial, ih (base + 1)⟩

theorem instruction_range_constraints_local (e : Expr)
    (he : e ∈ instructionAdd32RangeConstraints) : instructionLocalExpr e := by
  rcases List.mem_append.mp he with he | he
  · simp only [instructionAdd32Constraints, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with he | he | he | he <;> subst e <;> simp [instructionLocalExpr]
  · obtain ⟨limb, _, hm⟩ := List.mem_flatMap.mp he
    rcases List.mem_cons.mp hm with he | he
    · subst e
      exact ⟨rfl, instruction_bit_expr_local _ _⟩
    · obtain ⟨k, _, he⟩ := List.mem_map.mp he
      subst e
      simp [instructionBitConstraint, instructionLocalExpr]

/-- All range and arithmetic constraints are inherited from the actual AIR trace. -/
theorem instruction_range_trace_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = instructionAdd32RangeTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t) :
    instructionAdd32RangeHolds (tr.cell t r) := by
  intro e he
  have hc := holds.constr t ht r hr e
  rw [table] at hc
  have hv := hc he
  rw [instruction_local_eval e tr t r pub (instruction_range_constraints_local e he)] at hv
  exact hv

/-- No external limb-range premise is needed for the range-enforced trace. -/
theorem instruction_range_trace_binop (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = instructionAdd32RangeTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t) :
    Num.binop 32 0 (instructionAddWord (tr.cell t r) 0 1)
      (instructionAddWord (tr.cell t r) 2 3) =
      some (instructionAddWord (tr.cell t r) 4 5) :=
  instruction_add32_range_binop _
    (instruction_range_trace_holds air tr pub t ht table holds r hr)

end NearCompression
