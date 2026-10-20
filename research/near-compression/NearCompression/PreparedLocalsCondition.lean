import NearCompression.PreparedLocalsGas
import NearCompression.PreparedLocalsDepth
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536

/-- The branch-condition source expressions remain exact in the locals
profile; their positions move past local register constraints. -/
theorem prepared_locals_condition_source (count : Nat) :
    PreparedControlConditionSource (preparedLocalsLiteralExecTable count) := by
  refine ⟨(prepared_locals_gas_source count).boolean,?_,?_⟩
  · exact prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=960) (by decide))
  · exact prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=961) (by decide))

theorem prepared_locals_condition (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (hr : r<tr.height t) :
    ∃sp,sp<9 ∧ (∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) ∧
      (0<sp → (tr.cell t r 681).toNat≤1 ∧
        (tr.cell t r 681=0 ↔ preparedExecStackWord (tr.cell t r) (sp-1)=0)) := by
  obtain ⟨sp,bound,selected⟩:=prepared_locals_onehot count tr t r pub localH hr
  exact ⟨sp,bound,selected,fun positive=>prepared_control_condition_sound _ tr t r pub localH hr
    (prepared_locals_condition_source count) sp bound positive selected⟩
end NearCompression
