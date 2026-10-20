import NearCompression.InstructionSequence

/-! Output-to-right-operand links for a contiguous addition segment. This closes
an arbitrary replacement of the next right operand. The next left operand
stream is still unauthenticated; these are not full stack-consistency proofs. -/
namespace NearCompression
open NearSpecV3.Wasm ZkFormal.Air ZkFormal.Algebra

def instructionAdd32OperandPairs : List (Nat × Nat) := [(4, 2), (5, 3)]

def instructionAdd32OperandTable : Table :=
  instructionSequenceTable instructionAdd32SequenceTable instructionAdd32OperandPairs

theorem instruction_operand_control_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = instructionAdd32OperandTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t) :
    instructionAdd32ControlHolds (tr.cell t r) := by
  intro e he
  have h := holds.constr t ht r hr e
  rw [table] at h
  have hv := h (List.mem_append_left _ (List.mem_append_left _ he))
  rw [instruction_local_eval e tr t r pub (instruction_control_constraints_local e he)] at hv
  exact hv

/-- Both output limbs are linked to the next row's right operand. -/
theorem instruction_operand_right_link (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = instructionAdd32OperandTable)
    (holds : Holds air pub tr) (r : Nat) (next : r + 1 < tr.height t) :
    instructionAddWord (tr.cell t r) 4 5 = instructionAddWord (tr.cell t (r + 1)) 2 3 := by
  have lo := instruction_sequence_trace_link air tr pub t ht instructionAdd32SequenceTable
    instructionAdd32OperandPairs table holds r 4 2 (by simp [instructionAdd32OperandPairs]) next
  have hi := instruction_sequence_trace_link air tr pub t ht instructionAdd32SequenceTable
    instructionAdd32OperandPairs table holds r 5 3 (by simp [instructionAdd32OperandPairs]) next
  simp only [instructionAddWord, lo, hi]

/-- Each linked row still satisfies the actual Wasm addition operation. -/
theorem instruction_operand_row_binop (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = instructionAdd32OperandTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t) :
    Num.binop 32 0 (instructionAddWord (tr.cell t r) 0 1)
      (instructionAddWord (tr.cell t r) 2 3) =
      some (instructionAddWord (tr.cell t r) 4 5) := by
  exact instruction_add32_range_binop _ (instruction_control_addition_holds _
    (instruction_operand_control_holds air tr pub t ht table holds r hr))

/-- The next Wasm operation consumes the previous row's computed result. -/
theorem instruction_operand_recurrence (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = instructionAdd32OperandTable)
    (holds : Holds air pub tr) (r : Nat) (next : r + 1 < tr.height t) :
    Num.binop 32 0 (instructionAddWord (tr.cell t (r + 1)) 0 1)
      (instructionAddWord (tr.cell t r) 4 5) =
      some (instructionAddWord (tr.cell t (r + 1)) 4 5) := by
  rw [instruction_operand_right_link air tr pub t ht table holds r next]
  exact instruction_operand_row_binop air tr pub t ht table holds (r + 1) next

/-- Sum of the first `count` left operands, before reduction modulo 2^32. -/
def instructionOperandLeftSum (tr : Trace Fp) (t : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => instructionOperandLeftSum tr t count + instructionAddWord (tr.cell t count) 0 1

/-- Accumulated arithmetic is sound relative to the initial right operand and
the supplied left-operand stream. Authenticating that stream remains required. -/
theorem instruction_operand_accumulated_sum (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = instructionAdd32OperandTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t) :
    instructionAddWord (tr.cell t r) 4 5 =
      (instructionAddWord (tr.cell t 0) 2 3 + instructionOperandLeftSum tr t (r + 1)) % 4294967296 := by
  induction r with
  | zero =>
    have h := instruction_operand_row_binop air tr pub t ht table holds 0 hr
    simp only [Num.binop, Option.some.injEq] at h
    simpa only [instructionOperandLeftSum, Nat.zero_add, Nat.add_comm] using h.symm
  | succ r ih =>
    have prev := ih (by omega)
    have h := instruction_operand_recurrence air tr pub t ht table holds r hr
    simp only [Num.binop, Option.some.injEq] at h
    rw [prev] at h
    rw [← h]
    change (instructionAddWord (tr.cell t (r + 1)) 0 1 +
      (instructionAddWord (tr.cell t 0) 2 3 + instructionOperandLeftSum tr t (r + 1)) % 4294967296) %
      4294967296 = _
    rw [Nat.add_mod_mod]
    simp only [instructionOperandLeftSum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

set_option maxRecDepth 8192 in
theorem instruction_operand_table_wf :
    instructionAdd32OperandTable.wf ⟨[instructionAdd32OperandTable], 0, 0⟩ 2 = true := by
  decide

set_option maxRecDepth 8192 in
theorem instruction_operand_table_size :
    instructionAdd32OperandTable.width = 225 ∧
      instructionAdd32OperandTable.constraints.length = 236 := by
  decide

end NearCompression
