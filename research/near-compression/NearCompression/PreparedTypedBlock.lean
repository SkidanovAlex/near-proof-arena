import NearCompression.PreparedTypedSequential
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
private theorem block_at : ∀count:Fin 5,(preparedTypedLiteralExec count)[1666+66*(4-count.val)]?=some preparedLocalsLiteralExec1045 := by decide
theorem prepared_typed_block_label (count : Nat) (hc : count≤4) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (block : tr.cell t r 605=1) :
    tr.cell t r 639=0 ∧ tr.cell t (r+1) 639=1 ∧
    (∀ i,i<9 → tr.cell t (r+1) (640+i)=tr.cell t r (32+i)) ∧
    (∀ i,i<2 → preparedCodeLimb (tr.cell t (r+1)) (649+16*i)=preparedCodeLimb (tr.cell t r) (607+16*i)) ∧
    preparedCodeExecPC (tr.cell t (r+1))=preparedCodeExecPC (tr.cell t r)+1 ∧
    tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have ops:=prepared_typed_opcode_selected count hc tr t r pub localH (by omega) 4 (by decide) block
  have endZero : tr.cell t r 469=0:=ops 3 (by decide)
  have branchZero : tr.cell t r 606=0:=ops 5 (by decide)
  have success : preparedExecGasSuccess.eval tr t r pub=1 := by
    change ((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430)=1
    rw [active,charged];grind
  have member : preparedLocalsLiteralExec1045∈(preparedTypedLiteralExecTable count).constraints:=
    List.mem_of_getElem? (block_at ⟨count,by omega⟩)
  have guard:=localH.constr r (by omega) _ member
  change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 605*tr.cell t r 639)+ -(0:Fp)=0 at guard
  rw [success,block] at guard
  have absent : tr.cell t r 639=0:=by grind
  have taken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [branchZero];grind
  have opened : preparedControlOpened.eval tr t r pub=1 := by
    change preparedExecGasSuccess.eval tr t r pub*tr.cell t r 605=1
    rw [success,block];grind
  have keep : preparedControlKeep.eval tr t r pub=0 := by
    change (1:Fp)+ -(preparedControlOpened.eval tr t r pub+
      (preparedControlTaken.eval tr t r pub+preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 469*tr.cell t r 639)))=0
    rw [opened,taken,endZero];grind
  have advance : preparedControlAdvance.eval tr t r pub=Fp.ofNat 1 := by
    change preparedExecGasSuccess.eval tr t r pub*((1:Fp)+ -(tr.cell t r 469*((1:Fp)+ -tr.cell t r 639)+tr.cell t r 606*tr.cell t r 681))=1
    rw [success,endZero,branchZero];grind
  have labels:=prepared_typed_label_equations count hc tr t r pub localH nonlast
  rw [opened,keep] at labels
  have status:=prepared_typed_continue_status count hc tr t r pub localH nonlast active charged (by rw [endZero];grind)
  refine ⟨absent,by grind,?_,?_,prepared_typed_sequential_pc count hc tr t r pub localH nonlast taken 1 (by decide) advance,status.2.1,status.2.2⟩
  · intro i hi;have h:=labels.2.1 i hi;grind
  · intro i hi;have h:=labels.2.2 i hi;grind

/-- Nested end removes the saved label and advances without terminating
its enclosing function. Stack equality is a separate projection. -/
theorem prepared_typed_nested_end_label (count : Nat) (hc : count≤4) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (endOp : tr.cell t r 469=1) (nested : tr.cell t r 639=1) :
    tr.cell t (r+1) 639=0 ∧
    (∀ i,i<9 → tr.cell t (r+1) (640+i)=0) ∧
    preparedControlSavedTarget (tr.cell t (r+1))=0 ∧
    preparedCodeExecPC (tr.cell t (r+1))=preparedCodeExecPC (tr.cell t r)+1 ∧
    tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have ops:=prepared_typed_opcode_selected count hc tr t r pub localH (by omega) 3 (by decide) endOp
  have blockZero : tr.cell t r 605=0:=ops 4 (by decide)
  have branchZero : tr.cell t r 606=0:=ops 5 (by decide)
  have success : preparedExecGasSuccess.eval tr t r pub=1 := by
    change ((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430)=1
    rw [active,charged];grind
  have taken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [branchZero];grind
  have opened : preparedControlOpened.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*tr.cell t r 605=0
    rw [blockZero];grind
  have keep : preparedControlKeep.eval tr t r pub=0 := by
    change (1:Fp)+ -(preparedControlOpened.eval tr t r pub+
      (preparedControlTaken.eval tr t r pub+preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 469*tr.cell t r 639)))=0
    rw [opened,taken,success,endOp,nested];grind
  have advance : preparedControlAdvance.eval tr t r pub=Fp.ofNat 1 := by
    change preparedExecGasSuccess.eval tr t r pub*((1:Fp)+ -(tr.cell t r 469*((1:Fp)+ -tr.cell t r 639)+tr.cell t r 606*tr.cell t r 681))=1
    rw [success,nested,branchZero];grind
  have labels:=prepared_typed_label_equations count hc tr t r pub localH nonlast
  rw [opened,keep] at labels
  have status:=prepared_typed_continue_status count hc tr t r pub localH nonlast active charged (by rw [nested];grind)
  refine ⟨by grind,?_,?_,prepared_typed_sequential_pc count hc tr t r pub localH nonlast taken 1 (by decide) advance,status.2.1,status.2.2⟩
  · intro i hi;have h:=labels.2.1 i hi;grind
  · have low:=labels.2.2 0 (by decide)
    have high:=labels.2.2 1 (by decide)
    have l : preparedCodeLimb (tr.cell t (r+1)) 649=0:=by grind
    have h : preparedCodeLimb (tr.cell t (r+1)) 665=0:=by grind
    unfold preparedControlSavedTarget
    rw [l,h];rfl

end NearCompression
