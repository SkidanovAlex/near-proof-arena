import NearCompression.PreparedTypedLocalStack
import NearCompression.PreparedTypedEqzArray
import NearCompression.PreparedLocalsStackState
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem prepared_typed_local_stack_value (kind : PreparedLocalOp) (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (old : ∀i,i<3 → tr.cell t r (466+i)=0) (branch : tr.cell t r 606=0)
    (typed : ∀i,i<3 → tr.cell t r (1280+i)=0)
    (get : tr.cell t r 683=if kind=.get then 1 else 0) (set : tr.cell t r 684=if kind=.set then 1 else 0)
    (sp index : Nat) (sb : sp<9) (ib : index<4)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (selected : ∀i,i<4 → tr.cell t r (814+i)=if i=index then 1 else 0)
    (slot : Nat) (hs : slot<8) :
    preparedTypedStackValue (tr.cell t (r+1)) slot=
      if kind=.get ∧ slot=sp then preparedTypedLocalValue (tr.cell t r) index
      else if kind=.set ∧ slot+1=sp then .i32 0 else preparedTypedStackValue (tr.cell t r) slot := by
  have limbs:=prepared_typed_local_stack_limb kind count hc tr t r pub localH nonlast active charged old branch typed get set sp index sb ib hot selected slot
  have tag:=prepared_typed_local_stack_tag kind count hc tr t r pub localH nonlast active charged old branch typed get set sp index sb ib hot selected slot hs
  have a:=limbs 0 hs (by decide)
  have b:=limbs 1 hs (by decide)
  have c:=limbs 2 hs (by decide)
  have d:=limbs 3 hs (by decide)
  unfold preparedTypedStackValue preparedTypedStackWord instructionAdd64Word
  rw [tag,a,b,c,d]
  by_cases push : kind=.get ∧ slot=sp
  · simp only [push,ite_true]
    rfl
  · by_cases pop : kind=.set ∧ slot+1=sp
    · simp only [push,pop,ite_false,ite_true]
      rfl
    · simp only [push,pop,ite_false]

/-- Exact push/pop/unchanged array operations from typed value writes. This
lemma is representation algebra; the preceding theorem supplies its values
from actual literal AIR constraints. -/
theorem prepared_typed_local_stack_arrays (kind : PreparedLocalOp)
    (row next : Nat→Fp) (sp index : Nat)
    (valid : if kind=.get then sp<8 else 0<sp ∧ sp<9)
    (values : ∀slot,slot<8 → preparedTypedStackValue next slot=
      if kind=.get ∧ slot=sp then preparedTypedLocalValue row index
      else if kind=.set ∧ slot+1=sp then .i32 0 else preparedTypedStackValue row slot) :
    preparedTypedStack next (preparedLocalsNextDepth kind sp)=
      match kind with
      | .get => (preparedTypedStack row sp).push (preparedTypedLocalValue row index)
      | .set => (preparedTypedStack row sp).pop
      | .tee => preparedTypedStack row sp := by
  cases kind with
  | get =>
    simp only [reduceCtorEq,ite_true] at valid
    change preparedTypedStack next (sp+1)=_
    rw [prepared_typed_stack_succ]
    have same : preparedTypedStack next sp=preparedTypedStack row sp := by
      apply prepared_typed_stack_congr
      intro i hi
      simpa only [reduceCtorEq,true_and,false_and,show ¬i=sp by omega,ite_false] using values i (by omega)
    rw [same]
    have last:=values sp valid
    simpa using congrArg (Array.push (preparedTypedStack row sp)) last
  | set =>
    simp only [reduceCtorEq,ite_false] at valid
    change preparedTypedStack next (sp-1)=_
    have same : preparedTypedStack next (sp-1)=preparedTypedStack row (sp-1) := by
      apply prepared_typed_stack_congr
      intro i hi
      simpa only [reduceCtorEq,true_and,false_and,show ¬i+1=sp by omega,ite_false] using values i (by omega)
    rw [same]
    have eq : sp=(sp-1)+1:=by omega
    have e:=prepared_typed_stack_succ row (sp-1)
    rw [←eq] at e
    rw [e]
    simp
  | tee =>
    simp only [reduceCtorEq,ite_false] at valid
    change preparedTypedStack next sp=_
    apply prepared_typed_stack_congr
    intro i hi
    simpa using values i (by omega)
end NearCompression
