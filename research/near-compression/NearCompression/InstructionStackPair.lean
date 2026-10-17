import NearCompression.InstructionAddStep

namespace NearCompression
open NearSpecV3.Wasm ZkFormal.Algebra

/-- Range-constrained output limbs encode a canonical i32 value. -/
theorem instruction_stack_output_bound (row : Nat → Fp)
    (h : instructionAdd32RangeHolds row) : instructionAddWord row 4 5 < 4294967296 := by
  have ranges := instruction_add32_range_sound row h
  have lo := ranges 4 (by decide)
  have hi := ranges 5 (by decide)
  unfold instructionAddWord
  omega

/-- Execute two actual numeric instructions; fetch, PC and gas are handled separately. -/
def instructionTwoAdds (s : St) : Except String St := do
  let first ← execNum s 0x6A
  execNum first 0x6A

/-- Binding the left-operand stream to the actual initial stack, and linking
first output to second right operand, suffices for exact two-instruction stack
execution. Authentication of those initial bindings is still external. -/
theorem instruction_stack_pair_exact (first second : Nat → Fp)
    (hfirst : instructionAdd32RangeHolds first)
    (hsecond : instructionAdd32RangeHolds second)
    (s : St) (a b c : UInt32)
    (firstLeft : instructionAddWord first 0 1 = b.toNat)
    (firstRight : instructionAddWord first 2 3 = c.toNat)
    (secondLeft : instructionAddWord second 0 1 = a.toNat)
    (linked : instructionAddWord second 2 3 = instructionAddWord first 4 5) :
    instructionTwoAdds (pushV (pushV (pushV s (.i32 a)) (.i32 b)) (.i32 c)) =
      .ok (pushI32 s (instructionAddWord second 4 5)) := by
  have firstPop : popN (pushV (pushV (pushV s (.i32 a)) (.i32 b)) (.i32 c)) =
      (instructionAddWord first 2 3, pushV (pushV s (.i32 a)) (.i32 b)) := by
    rw [firstRight]
    exact instruction_add32_pop_push _ _
  have secondPop : popN (pushV (pushV s (.i32 a)) (.i32 b)) =
      (instructionAddWord first 0 1, pushV s (.i32 a)) := by
    rw [firstLeft]
    exact instruction_add32_pop_push _ _
  have runFirst := instruction_add32_range_exec_num first hfirst _ _ _ firstPop secondPop
  have bound := instruction_stack_output_bound first hfirst
  have resultPop : popN (pushI32 (pushV s (.i32 a)) (instructionAddWord first 4 5)) =
      (instructionAddWord second 2 3, pushV s (.i32 a)) := by
    rw [linked]
    unfold pushI32
    rw [instruction_add32_pop_push]
    congr 1
    change instructionAddWord first 4 5 % 4294967296 = instructionAddWord first 4 5
    exact Nat.mod_eq_of_lt bound
  have leftPop : popN (pushV s (.i32 a)) = (instructionAddWord second 0 1, s) := by
    rw [secondLeft]
    exact instruction_add32_pop_push _ _
  have runSecond := instruction_add32_range_exec_num second hsecond _ _ _ resultPop leftPop
  unfold instructionTwoAdds
  rw [runFirst]
  change execNum (pushI32 (pushV s (.i32 a)) (instructionAddWord first 4 5)) 0x6A = _
  exact runSecond

end NearCompression
