import NearCompression.PreparedTypedSource
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def preparedTypedStackUpperGuard (slot high : Nat) : Expr :=
  .add (.mul (.add (.const 1) (.neg (.col (1074+slot) false)))
    (preparedCodeBits (818+32*slot+16*high))) (.neg (.const 0))

private theorem upper_at : ∀count:Fin 5,∀slot:Fin 8,∀high:Fin 2,
    (preparedTypedLiteralExec count)[1742+66*(4-count.val)+12*slot.val+3*high.val]?=
      some (preparedTypedStackUpperGuard slot high) := by decide

/-- Actual literal upper-word guards prohibit an i32 tagged value from
carrying nonzero hidden high bits. -/
theorem prepared_typed_stack_upper_zero (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (slot high : Nat) (hs : slot<8) (hh : high<2) (tag : tr.cell t r (1074+slot)=0) :
    preparedCodeLimb (tr.cell t r) (818+32*slot+16*high)=0 := by
  have member:=List.mem_of_getElem? (upper_at ⟨count,by omega⟩ ⟨slot,hs⟩ ⟨high,hh⟩)
  have h:=localH.constr r hr _ member
  change ((1:Fp)+ -tr.cell t r (1074+slot))*(preparedCodeBits (818+32*slot+16*high)).eval tr t r pub+ -(0:Fp)=0 at h
  rw [tag,prepared_code_bits_eval] at h
  grind

theorem prepared_typed_stack_i32_bound (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (slot : Nat) (hs : slot<8) (tag : tr.cell t r (1074+slot)=0) :
    preparedTypedStackWord (tr.cell t r) slot<2^32 := by
  have lo:=prepared_typed_stack_limb_bound count hc tr t r pub localH hr slot 0 hs (by decide)
  have hi:=prepared_typed_stack_limb_bound count hc tr t r pub localH hr slot 1 hs (by decide)
  have z2:=prepared_typed_stack_upper_zero count hc tr t r pub localH hr slot 0 hs (by decide) tag
  have z3:=prepared_typed_stack_upper_zero count hc tr t r pub localH hr slot 1 hs (by decide) tag
  simp only [preparedTypedStackWord,instructionAdd64Word,preparedTypedStackLimb,preparedTypedStackBase,
    Nat.reduceAdd,Nat.reduceLT,ite_true,ite_false,Nat.reduceMod,Nat.mul_zero,Nat.mul_one,Nat.add_zero] at lo hi ⊢
  simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero] at z2 z3
  rw [z2,z3]
  change _+_+4294967296*0+281474976710656*0<4294967296
  omega

def preparedTypedStackValue (row : Nat→Fp) (slot : Nat) : Val :=
  if row (1074+slot)=0 then .i32 (UInt32.ofNat (preparedTypedStackWord row slot))
  else .i64 (UInt64.ofNat (preparedTypedStackWord row slot))
def preparedTypedStack (row : Nat→Fp) (sp : Nat) : Array Val :=
  ((List.range sp).map (preparedTypedStackValue row)).toArray

theorem prepared_typed_stack_value_exact (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (slot : Nat) (hs : slot<8) :
    match preparedTypedStackValue (tr.cell t r) slot with
    | .i32 v=>v.toNat=preparedTypedStackWord (tr.cell t r) slot
    | .i64 v=>v.toNat=preparedTypedStackWord (tr.cell t r) slot
    | .ref _=>False := by
  by_cases tag:tr.cell t r (1074+slot)=0
  · simp only [preparedTypedStackValue,if_pos tag]
    exact Nat.mod_eq_of_lt (prepared_typed_stack_i32_bound count hc tr t r pub localH hr slot hs tag)
  · simp only [preparedTypedStackValue,if_neg tag]
    exact Nat.mod_eq_of_lt (prepared_typed_stack_word_bound count hc tr t r pub localH hr slot hs)

theorem prepared_typed_stack_lookup (row : Nat→Fp) (sp slot : Nat) (hs : slot<sp) :
    (preparedTypedStack row sp)[slot]?=some (preparedTypedStackValue row slot) := by
  simp [preparedTypedStack,hs]
end NearCompression
