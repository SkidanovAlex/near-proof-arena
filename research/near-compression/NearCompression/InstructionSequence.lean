import NearCompression.InstructionControlTrace

/-! Reusable noncyclic metadata links between adjacent trace rows. The
specialization is a contiguous addition-only segment, without padding or
mixed-opcode dispatch. No operand-stack/state bus is claimed by these links. -/
namespace NearCompression
open NearSpecV3.Wasm ZkFormal.Air ZkFormal.Algebra

def instructionSequenceConstraint (pair : Nat × Nat) : Expr :=
  .mul .isTransition (.add (.col pair.1 false) (.neg (.col pair.2 true)))

def instructionSequenceConstraints (pairs : List (Nat × Nat)) : List Expr :=
  pairs.map instructionSequenceConstraint

def instructionSequenceTable (base : Table) (pairs : List (Nat × Nat)) : Table :=
  { base with constraints := base.constraints ++ instructionSequenceConstraints pairs }

def instructionAdd32SequencePairs : List (Nat × Nat) := [(107, 105), (108, 106), (111, 110)]

def instructionAdd32SequenceTable : Table :=
  instructionSequenceTable instructionAdd32ControlTable instructionAdd32SequencePairs

/-- Actual AIR evaluation enforces equality at every nonfinal row. -/
theorem instruction_sequence_eval_link (tr : Trace Fp) (pub : List Fp)
    (t r post pre : Nat) (next : r + 1 < tr.height t)
    (h : (instructionSequenceConstraint (post, pre)).eval tr t r pub = 0) :
    tr.cell t r post = tr.cell t (r + 1) pre := by
  simp only [instructionSequenceConstraint, Expr.eval, Expr.evalWith, rowEnv,
    if_false, if_true, Nat.mod_eq_of_lt next, Nat.ne_of_lt next] at h
  change (1 : Fp) * (tr.cell t r post + -tr.cell t (r + 1) pre) = 0 at h
  grind

/-- The final row is deliberately not linked back to row zero. -/
theorem instruction_sequence_eval_final (tr : Trace Fp) (pub : List Fp)
    (t r post pre : Nat) (last : r + 1 = tr.height t) :
    (instructionSequenceConstraint (post, pre)).eval tr t r pub = 0 := by
  simp only [instructionSequenceConstraint, Expr.eval, Expr.evalWith, rowEnv,
    if_false, if_true, last]
  change (0 : Fp) * _ = 0
  grind

/-- Honest adjacent metadata values satisfy the same expression, including
its use of cyclic next-row indexing internally. -/
theorem instruction_sequence_eval_complete (tr : Trace Fp) (pub : List Fp)
    (t r post pre : Nat) (hr : r < tr.height t)
    (linked : r + 1 < tr.height t → tr.cell t r post = tr.cell t (r + 1) pre) :
    (instructionSequenceConstraint (post, pre)).eval tr t r pub = 0 := by
  by_cases last : r + 1 = tr.height t
  · exact instruction_sequence_eval_final tr pub t r post pre last
  · have next : r + 1 < tr.height t := by omega
    have eq := linked next
    simp only [instructionSequenceConstraint, Expr.eval, Expr.evalWith, rowEnv,
      if_false, if_true, Nat.mod_eq_of_lt next, last]
    change (1 : Fp) * (tr.cell t r post + -tr.cell t (r + 1) pre) = 0
    rw [eq]
    grind

/-- Generic extraction from the actual AIR semantic predicate. -/
theorem instruction_sequence_trace_link (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length) (base : Table) (pairs : List (Nat × Nat))
    (table : air.tables[t] = instructionSequenceTable base pairs)
    (holds : Holds air pub tr) (r post pre : Nat)
    (pair : (post, pre) ∈ pairs) (next : r + 1 < tr.height t) :
    tr.cell t r post = tr.cell t (r + 1) pre := by
  have h := holds.constr t ht r (by omega) (instructionSequenceConstraint (post, pre))
  rw [table] at h
  have he := h (List.mem_append_right _ (List.mem_map.mpr ⟨(post, pre), pair, rfl⟩))
  exact instruction_sequence_eval_link tr pub t r post pre next he

/-- Appending links preserves each row's arithmetic/control constraint proof. -/
theorem instruction_sequence_control_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = instructionAdd32SequenceTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t) :
    instructionAdd32ControlHolds (tr.cell t r) := by
  intro e he
  have h := holds.constr t ht r hr e
  rw [table] at h
  have hv := h (List.mem_append_left _ he)
  rw [instruction_local_eval e tr t r pub (instruction_control_constraints_local e he)] at hv
  exact hv

/-- Both PC limbs and the stack-height value agree between adjacent rows. -/
theorem instruction_sequence_metadata_link (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = instructionAdd32SequenceTable)
    (holds : Holds air pub tr) (r : Nat) (next : r + 1 < tr.height t) :
    instructionAddWord (tr.cell t r) 107 108 = instructionAddWord (tr.cell t (r + 1)) 105 106 ∧
    (tr.cell t r 111).toNat = (tr.cell t (r + 1) 110).toNat := by
  have lo := instruction_sequence_trace_link air tr pub t ht instructionAdd32ControlTable
    instructionAdd32SequencePairs table holds r 107 105 (by simp [instructionAdd32SequencePairs]) next
  have hi := instruction_sequence_trace_link air tr pub t ht instructionAdd32ControlTable
    instructionAdd32SequencePairs table holds r 108 106 (by simp [instructionAdd32SequencePairs]) next
  have height := instruction_sequence_trace_link air tr pub t ht instructionAdd32ControlTable
    instructionAdd32SequencePairs table holds r 111 110 (by simp [instructionAdd32SequencePairs]) next
  constructor
  · simp only [instructionAddWord, lo, hi]
  · rw [height]

/-- Exact progression of local PC and height through an addition-only segment. -/
theorem instruction_sequence_metadata_progression (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = instructionAdd32SequenceTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t) :
    instructionAddWord (tr.cell t r) 105 106 = instructionAddWord (tr.cell t 0) 105 106 + r ∧
    (tr.cell t r 110).toNat + r = (tr.cell t 0 110).toNat := by
  induction r with
  | zero => simp
  | succ r ih =>
    have prev := ih (by omega)
    have link := instruction_sequence_metadata_link air tr pub t ht table holds r hr
    have metadata := instruction_control_metadata_sound (tr.cell t r)
      (instruction_sequence_control_holds air tr pub t ht table holds r (by omega))
    constructor
    · have step := metadata.2.1
      rw [link.1] at step
      omega
    · have step := metadata.2.2.2.2.2.1
      rw [link.2] at step
      omega

set_option maxRecDepth 8192 in
theorem instruction_sequence_table_wf :
    instructionAdd32SequenceTable.wf ⟨[instructionAdd32SequenceTable], 0, 0⟩ 2 = true := by
  decide

set_option maxRecDepth 8192 in
theorem instruction_sequence_table_size :
    instructionAdd32SequenceTable.width = 225 ∧
      instructionAdd32SequenceTable.constraints.length = 234 := by
  decide

/-- A contiguous addition-only trace consumes one stack item per row.
Its finite stack bound is stricter than the verifier's configured height cap. -/
theorem instruction_sequence_capacity (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = instructionAdd32SequenceTable)
    (holds : Holds air pub tr) :
    tr.height t + 1 ≤ (tr.cell t 0 110).toNat ∧ tr.log t ≤ 15 := by
  have positive : 0 < tr.height t := Nat.two_pow_pos _
  have last : tr.height t - 1 < tr.height t := by omega
  have progression := instruction_sequence_metadata_progression air tr pub t ht table holds
    (tr.height t - 1) last
  have lastMetadata := instruction_control_metadata_sound (tr.cell t (tr.height t - 1))
    (instruction_sequence_control_holds air tr pub t ht table holds (tr.height t - 1) last)
  have firstMetadata := instruction_control_metadata_sound (tr.cell t 0)
    (instruction_sequence_control_holds air tr pub t ht table holds 0 positive)
  have hlast := lastMetadata.2.2.2.2.1
  have hfirst := firstMetadata.2.2.2.2.2.2
  have capacity : tr.height t + 1 ≤ (tr.cell t 0 110).toNat := by omega
  refine ⟨capacity, ?_⟩
  by_cases bound : tr.log t ≤ 15
  · exact bound
  · have powBound : 2 ^ 16 ≤ 2 ^ tr.log t := Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
    change 65536 ≤ tr.height t at powBound
    omega

end NearCompression
