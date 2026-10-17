import NearCompression.PreparedControlSequential

set_option maxRecDepth 65536
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm

def preparedControlOpcodeColumn (i : Nat) : Nat := if i<4 then 466+i else 605+(i-4)

theorem prepared_control_opcode_selected (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (hr : r<tr.height t) :
    ∃ tag, tag<6 ∧ ∀ i,i<6 → tr.cell t r (preparedControlOpcodeColumn i)=if i=tag then 1 else 0 := by
  let code : Nat → Nat:=fun i=>if i<4 then 466+i else 605+(i-4)
  have one : ∃ tag,tag<6 ∧ ∀ i,i<6 → tr.cell t r (code i)=if i=tag then 1 else 0 := by
    suffices h : ∃ tag,tag<6 ∧ ∀ i,i<6 → tr.cell t r (code (0+i))=if i=tag then 1 else 0 by
      simpa only [Nat.zero_add] using h
    apply prepared_onehot 6 0 (fun i=>tr.cell t r (code i)) (by decide)
    · intro i hi
      apply prepared_control_literal_boolean tr t r pub localH hr
      dsimp only [code]
      split <;> omega
    · have member : preparedControlLiteralExec0685∈preparedControlLiteralExecTable.constraints:=
        List.getElem_mem (l:=preparedControlLiteralExec) (n:=685) (by decide)
      have h:=localH.constr r hr _ member
      change ((tr.cell t r 466+tr.cell t r 467)+(tr.cell t r 468+tr.cell t r 469)+
        (tr.cell t r 605+tr.cell t r 606))+ -(1:Fp)=0 at h
      simp only [preparedFieldSum,code,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,ite_true,ite_false]
      grind
  exact one

theorem prepared_control_opcode_exclusive (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (hr : r<tr.height t)
    (tag : Nat) (bound : tag<6) (chosen : tr.cell t r (preparedControlOpcodeColumn tag)=1) :
    ∀ i,i<6 → tr.cell t r (preparedControlOpcodeColumn i)=if i=tag then 1 else 0 := by
  obtain ⟨j,hj,selected⟩:=prepared_control_opcode_selected tr t r pub localH hr
  have h:=selected tag bound
  rw [chosen] at h
  have eq : tag=j := by
    by_cases eq:tag=j
    · exact eq
    · simp only [eq,ite_false] at h
      exact False.elim ((by decide : (1:Fp)≠0) h)
  simpa only [←eq] using selected

/-- A successful block opens exactly one void label, recording current SP
and the authenticated target columns. This does not authenticate CODE by itself. -/
theorem prepared_control_block_label (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (block : tr.cell t r 605=1) :
    tr.cell t r 639=0 ∧ tr.cell t (r+1) 639=1 ∧
    (∀ i,i<9 → tr.cell t (r+1) (640+i)=tr.cell t r (32+i)) ∧
    (∀ i,i<2 → preparedCodeLimb (tr.cell t (r+1)) (649+16*i)=preparedCodeLimb (tr.cell t r) (607+16*i)) ∧
    preparedCodeExecPC (tr.cell t (r+1))=preparedCodeExecPC (tr.cell t r)+1 ∧
    tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have ops:=prepared_control_opcode_exclusive tr t r pub localH (by omega) 4 (by decide) block
  have endZero : tr.cell t r 469=0:=ops 3 (by decide)
  have branchZero : tr.cell t r 606=0:=ops 5 (by decide)
  have success : preparedExecGasSuccess.eval tr t r pub=1 := by
    change ((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430)=1
    rw [active,charged];grind
  have member : preparedControlLiteralExec0771∈preparedControlLiteralExecTable.constraints:=
    List.getElem_mem (l:=preparedControlLiteralExec) (n:=771) (by decide)
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
  have labels:=prepared_control_label_equations tr t r pub localH nonlast
  rw [opened,keep] at labels
  have status:=prepared_control_continue_status tr t r pub localH nonlast active charged (by rw [endZero];grind)
  refine ⟨absent,by grind,?_,?_,prepared_control_sequential_pc tr t r pub localH nonlast taken 1 (by decide) advance,status.2.1,status.2.2⟩
  · intro i hi;have h:=labels.2.1 i hi;grind
  · intro i hi;have h:=labels.2.2 i hi;grind

/-- Nested end removes the saved label and advances without terminating
its enclosing function. Stack equality is a separate projection. -/
theorem prepared_control_nested_end_label (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (endOp : tr.cell t r 469=1) (nested : tr.cell t r 639=1) :
    tr.cell t (r+1) 639=0 ∧
    (∀ i,i<9 → tr.cell t (r+1) (640+i)=0) ∧
    preparedControlSavedTarget (tr.cell t (r+1))=0 ∧
    preparedCodeExecPC (tr.cell t (r+1))=preparedCodeExecPC (tr.cell t r)+1 ∧
    tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have ops:=prepared_control_opcode_exclusive tr t r pub localH (by omega) 3 (by decide) endOp
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
  have labels:=prepared_control_label_equations tr t r pub localH nonlast
  rw [opened,keep] at labels
  have status:=prepared_control_continue_status tr t r pub localH nonlast active charged (by rw [nested];grind)
  refine ⟨by grind,?_,?_,prepared_control_sequential_pc tr t r pub localH nonlast taken 1 (by decide) advance,status.2.1,status.2.2⟩
  · intro i hi;have h:=labels.2.1 i hi;grind
  · have low:=labels.2.2 0 (by decide)
    have high:=labels.2.2 1 (by decide)
    have l : preparedCodeLimb (tr.cell t (r+1)) 649=0:=by grind
    have h : preparedCodeLimb (tr.cell t (r+1)) 665=0:=by grind
    unfold preparedControlSavedTarget
    rw [l,h];rfl

end NearCompression
