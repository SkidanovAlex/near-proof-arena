import NearCompression.PreparedTypedBranchStack
import NearCompression.PreparedTypedBranchBounds
import NearCompression.PreparedTypedEqzArray
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536

theorem prepared_typed_stack_extract (row : Nat→Fp) (n height : Nat) (bound : height≤n) :
    (preparedTypedStack row n).extract 0 height=preparedTypedStack row height := by
  induction n with
  | zero =>
    have h:height=0:=by omega
    subst height
    rfl
  | succ n ih =>
    by_cases small:height≤n
    · rw [prepared_typed_stack_succ,Array.extract_push_of_le (by simp [preparedTypedStack];exact small)]
      exact ih small
    · have eq:height=n+1:=by omega
      subst height
      exact Array.extract_eq_self_of_le (by simp [preparedTypedStack])

theorem prepared_typed_stack_i32_word (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (slot : Nat) (hs : slot<8) (tag : tr.cell t r (1074+slot)=0) :
    preparedTypedStackWord (tr.cell t r) slot=preparedExecStackWord (tr.cell t r) slot := by
  have z2:=prepared_typed_stack_upper_zero count hc tr t r pub localH hr slot 0 hs (by decide) tag
  have z3:=prepared_typed_stack_upper_zero count hc tr t r pub localH hr slot 1 hs (by decide) tag
  simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero] at z2 z3
  rw [prepared_control_stack_word]
  unfold preparedTypedStackWord instructionAdd64Word preparedTypedStackLimb preparedTypedStackBase
  simp only [Nat.reduceAdd,Nat.reduceLT,ite_true,ite_false,Nat.reduceMod,Nat.mul_zero,Nat.mul_one,Nat.add_zero]
  rw [z2,z3]
  change _+_+4294967296*0+281474976710656*0=_
  omega

/-- Only live stack slots are needed by the actual interpreter. Untaken
branches preserve the pop prefix; taken branches preserve the saved prefix.
Every slot retains its exact Val tag and all64 possible value bits. -/
theorem prepared_typed_branch_array (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (branch : tr.cell t r 606=1)
    (taken : Bool) (flag : tr.cell t r 681=if taken then 1 else 0)
    (sp height : Nat) (sb : sp<9) (hb : height<9) (lt : height<sp)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (saved : ∀i,i<9 → tr.cell t r (640+i)=if i=height then 1 else 0) :
    preparedTypedStack (tr.cell t (r+1)) (if taken then height else sp-1)=
      if taken then (preparedTypedStack (tr.cell t r) (sp-1)).extract 0 height
      else preparedTypedStack (tr.cell t r) (sp-1) := by
  cases taken with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at flag ⊢
    apply prepared_typed_stack_congr
    intro i hi
    exact prepared_typed_branch_stack_value count hc tr t r pub localH nonlast active charged branch false flag sp height sb hb hot saved i (by omega) (by simp;omega)
  | true =>
    simp only [ite_true] at flag ⊢
    rw [prepared_typed_stack_extract _ _ _ (by omega)]
    apply prepared_typed_stack_congr
    intro i hi
    exact prepared_typed_branch_stack_value count hc tr t r pub localH nonlast active charged branch true flag sp height sb hb hot saved i (by omega) hi
end NearCompression
