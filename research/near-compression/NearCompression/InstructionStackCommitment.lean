import NearCompression.InstructionStackPair
import NearCompression.ValueWire

/-! Full initial-stack openings for two consecutive additions. Hash checking
is an executable check outside AIR, not a succinct authentication circuit or
a quantum-security theorem. Typed codecs and their bounds are reused. -/
namespace NearCompression
open NearSpec NearSpecV3.Wasm ZkFormal.Algebra

def instructionStackDomain : Bytes := "nearproof-stack-v1".toUTF8.data.toList

def encodeInstructionStack (stack : Array Val) : Bytes :=
  instructionStackDomain ++ encodeStackWire stack

def checkInstructionValueWireWf : Val → Bool
  | .i32 _ | .i64 _ => true
  | .ref none => true
  | .ref (some n) => decide (n < 18446744073709551616)

def checkInstructionStackWireWf (stack : Array Val) : Bool :=
  decide (stack.size < 4294967296) && stack.toList.all checkInstructionValueWireWf

theorem instruction_stack_value_wf_check (v : Val) :
    checkInstructionValueWireWf v = true ↔ valueWireWf v := by
  cases v with
  | i32 v => simp [checkInstructionValueWireWf, valueWireWf]
  | i64 v => simp [checkInstructionValueWireWf, valueWireWf]
  | ref r => cases r <;> simp [checkInstructionValueWireWf, valueWireWf]

theorem instruction_stack_wf_check (stack : Array Val) :
    checkInstructionStackWireWf stack = true ↔ stackWireWf stack := by
  simp only [checkInstructionStackWireWf, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, instruction_stack_value_wf_check, stackWireWf, Array.length_toList]

theorem instruction_stack_encoding_injective (a b : Array Val)
    (ha : stackWireWf a) (hb : stackWireWf b)
    (eq : encodeInstructionStack a = encodeInstructionStack b) : a = b := by
  have wireEq : encodeStackWire a = encodeStackWire b := List.append_cancel_left eq
  have parsed := congrArg (fun bs => parseStackWire (bs ++ [])) wireEq
  rw [stack_wire_roundtrip a ha [], stack_wire_roundtrip b hb []] at parsed
  exact congrArg Prod.fst (Except.ok.inj parsed)

def instructionStackCollision (hash : Bytes → ByteArray) (actual claimed : Array Val) : Prop :=
  encodeInstructionStack actual ≠ encodeInstructionStack claimed ∧
    hash (encodeInstructionStack actual) = hash (encodeInstructionStack claimed)

theorem instruction_stack_binding_or_collision (hash : Bytes → ByteArray)
    (actual claimed : Array Val) (ha : stackWireWf actual) (hc : stackWireWf claimed)
    (eq : hash (encodeInstructionStack actual) = hash (encodeInstructionStack claimed)) :
    actual = claimed ∨ instructionStackCollision hash actual claimed := by
  by_cases same : encodeInstructionStack actual = encodeInstructionStack claimed
  · exact Or.inl (instruction_stack_encoding_injective actual claimed ha hc same)
  · exact Or.inr ⟨same, eq⟩

structure InstructionStackOpening where
  «prefix» : Array Val
  a : UInt32
  b : UInt32
  c : UInt32

def instructionStackOpeningStack (opening : InstructionStackOpening) : Array Val :=
  ((opening.prefix.push (.i32 opening.a)).push (.i32 opening.b)).push (.i32 opening.c)

def checkInstructionStackOpening (hash : Bytes → ByteArray) (expectedRoot : ByteArray)
    (opening : InstructionStackOpening) : Bool :=
  checkInstructionStackWireWf (instructionStackOpeningStack opening) &&
    decide (expectedRoot = hash (encodeInstructionStack (instructionStackOpeningStack opening)))

def checkInstructionStackPair (hash : Bytes → ByteArray) (expectedRoot : ByteArray)
    (first second : Nat → Fp) (opening : InstructionStackOpening) : Bool :=
  checkInstructionStackOpening hash expectedRoot opening &&
    decide (instructionAddWord first 0 1 = opening.b.toNat) &&
    decide (instructionAddWord first 2 3 = opening.c.toNat) &&
    decide (instructionAddWord second 0 1 = opening.a.toNat) &&
    decide (instructionAddWord second 2 3 = instructionAddWord first 4 5) &&
    decide ((first 110).toNat = (instructionStackOpeningStack opening).size) &&
    decide ((second 110).toNat + 1 = (instructionStackOpeningStack opening).size)

theorem instruction_stack_opening_correct (hash : Bytes → ByteArray) (actual : Array Val)
    (ha : stackWireWf actual) (opening : InstructionStackOpening)
    (accepted : checkInstructionStackOpening hash (hash (encodeInstructionStack actual)) opening = true) :
    actual = instructionStackOpeningStack opening ∨
      instructionStackCollision hash actual (instructionStackOpeningStack opening) := by
  simp only [checkInstructionStackOpening, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact instruction_stack_binding_or_collision hash actual _ ha
    ((instruction_stack_wf_check _).mp accepted.1) accepted.2

/-- Accepted initial-stack authentication and two AIR arithmetic rows imply
exact execution on the actual state, or exhibit two distinct colliding messages. -/
theorem instruction_stack_pair_committed (hash : Bytes → ByteArray)
    (first second : Nat → Fp)
    (hfirst : instructionAdd32RangeHolds first) (hsecond : instructionAdd32RangeHolds second)
    (s : St) (ha : stackWireWf s.stack) (opening : InstructionStackOpening)
    (accepted : checkInstructionStackPair hash (hash (encodeInstructionStack s.stack))
      first second opening = true) :
    instructionTwoAdds s = .ok (pushI32 { s with stack := opening.prefix }
      (instructionAddWord second 4 5)) ∨
    instructionStackCollision hash s.stack (instructionStackOpeningStack opening) := by
  simp only [checkInstructionStackPair, Bool.and_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨⟨⟨⟨⟨⟨opened, firstLeft⟩, firstRight⟩, secondLeft⟩, linked⟩, _⟩, _⟩ := accepted
  rcases instruction_stack_opening_correct hash s.stack ha opening opened with same | collision
  · have stateEq : s = pushV (pushV (pushV { s with stack := opening.prefix }
        (.i32 opening.a)) (.i32 opening.b)) (.i32 opening.c) := by
      change s = { s with stack := instructionStackOpeningStack opening }
      rw [← same]
    have execution := instruction_stack_pair_exact first second hfirst hsecond
      { s with stack := opening.prefix } opening.a opening.b opening.c
      firstLeft firstRight secondLeft linked
    rw [← stateEq] at execution
    exact Or.inl execution
  · exact Or.inr collision

theorem instruction_stack_opening_complete (hash : Bytes → ByteArray)
    (opening : InstructionStackOpening) (wf : stackWireWf (instructionStackOpeningStack opening)) :
    checkInstructionStackOpening hash
      (hash (encodeInstructionStack (instructionStackOpeningStack opening))) opening = true := by
  simp only [checkInstructionStackOpening, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨(instruction_stack_wf_check _).mpr wf, trivial⟩

/-- Stack-height metadata is tied to the size of the authenticated opening. -/
theorem instruction_stack_pair_height_bindings (hash : Bytes → ByteArray) (root : ByteArray)
    (first second : Nat → Fp) (opening : InstructionStackOpening)
    (accepted : checkInstructionStackPair hash root first second opening = true) :
    (first 110).toNat = (instructionStackOpeningStack opening).size ∧
      (second 110).toNat + 1 = (instructionStackOpeningStack opening).size := by
  simp only [checkInstructionStackPair, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ⟨accepted.1.2, accepted.2⟩

/-- These height bindings refer to the actual initial stack, unless the two
explicit committed stack messages collide. -/
theorem instruction_stack_pair_committed_heights (hash : Bytes → ByteArray)
    (first second : Nat → Fp) (actual : Array Val) (wf : stackWireWf actual)
    (opening : InstructionStackOpening)
    (accepted : checkInstructionStackPair hash (hash (encodeInstructionStack actual))
      first second opening = true) :
    ((first 110).toNat = actual.size ∧ (second 110).toNat + 1 = actual.size) ∨
      instructionStackCollision hash actual (instructionStackOpeningStack opening) := by
  have heights := instruction_stack_pair_height_bindings hash _ first second opening accepted
  simp only [checkInstructionStackPair, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have opened := accepted.1.1.1.1.1.1
  rcases instruction_stack_opening_correct hash actual wf opening opened with same | collision
  · exact Or.inl (same ▸ heights)
  · exact Or.inr collision

end NearCompression
