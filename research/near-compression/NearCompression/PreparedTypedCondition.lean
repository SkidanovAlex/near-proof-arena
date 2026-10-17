import NearCompression.PreparedTypedLocalUpdate
import NearCompression.PreparedTypedGas
import NearCompression.PreparedTypedOpcode
import NearCompression.PreparedTypedLocalDepth
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem inverse_at : ∀count:Fin 5,(preparedTypedLiteralExec count)[1581+66*(4-count.val)]?=some preparedControlConditionInverse := by decide
private theorem zero_at : ∀count:Fin 5,(preparedTypedLiteralExec count)[1582+66*(4-count.val)]?=some preparedControlConditionZero := by decide
private theorem pop_at : ∀count:Fin 5,(preparedTypedLiteralExec count)[1664+66*(4-count.val)]?=some preparedTypedPopGuard := by decide
private theorem type_at : ∀count:Fin 5,(preparedTypedLiteralExec count)[1559+66*(4-count.val)]?=
  some (.mul (.mul preparedExecGasSuccess (.add (.col 467 false) (.col 606 false))) (.add preparedTypedSelectedType (.neg (.const 0)))) := by decide

theorem prepared_typed_condition_source (count : Nat) (hc : count≤4) :
    PreparedControlConditionSource (preparedTypedLiteralExecTable count) := by
  exact ⟨(prepared_typed_gas_source count hc).boolean,
    List.mem_of_getElem? (inverse_at ⟨count,by omega⟩),List.mem_of_getElem? (zero_at ⟨count,by omega⟩)⟩

/-- The branch operand is nonempty and actually i32-tagged. The zero test
uses its lower32 bits, whose agreement with its typed value follows from
the literal i32 upper-limb guards. -/
theorem prepared_typed_branch_operand (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (branch : tr.cell t r 606=1)
    (sp : Nat) (bound : sp<9) (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    0<sp ∧ tr.cell t r (1074+(sp-1))=0 ∧
      (tr.cell t r 681=0 ↔ preparedExecStackWord (tr.cell t r) (sp-1)=0) := by
  have flags:=prepared_typed_opcode_selected count hc tr t r pub localH hr 5 (by decide) branch
  have add0:=flags 1 (by decide);have drop0:=flags 2 (by decide)
  have set0:=flags 7 (by decide);have tee0:=flags 8 (by decide);have eqz0:=flags 11 (by decide)
  change tr.cell t r 467=0 at add0
  change tr.cell t r 468=0 at drop0
  change tr.cell t r 684=0 at set0
  change tr.cell t r 685=0 at tee0
  change tr.cell t r 1282=0 at eqz0
  have pop:=localH.constr r hr _ (List.mem_of_getElem? (pop_at ⟨count,by omega⟩))
  change (((1:Fp)+ -tr.cell t r 41)*(1+ -tr.cell t r 430))*
    (((tr.cell t r 468+tr.cell t r 606)+(tr.cell t r 684+tr.cell t r 685)+tr.cell t r 1282)*tr.cell t r 32)+ -0=0 at pop
  rw [active,charged,drop0,branch,set0,tee0,eqz0] at pop
  have pos:0<sp:=by
    by_cases z:sp=0
    · have h:=hot 0 (by decide);rw [z] at h
      simp only [ite_true] at h
      rw [h] at pop
      have bad:(1:Fp)=0:=by grind
      exact False.elim ((by decide:(1:Fp)≠0) bad)
    · omega
  have typ:=localH.constr r hr _ (List.mem_of_getElem? (type_at ⟨count,by omega⟩))
  change (((1:Fp)+ -tr.cell t r 41)*(1+ -tr.cell t r 430)*(tr.cell t r 467+tr.cell t r 606))*
    (preparedTypedSelectedType.eval tr t r pub+ -0)=0 at typ
  rw [active,charged,add0,branch,prepared_typed_selected_type_eval tr t r pub sp bound pos hot] at typ
  exact ⟨pos,by grind,(prepared_control_condition_sound _ tr t r pub localH hr
    (prepared_typed_condition_source count hc) sp bound pos hot).2⟩
end NearCompression
