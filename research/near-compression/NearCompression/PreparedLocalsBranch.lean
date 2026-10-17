import NearCompression.PreparedLocalsOpcode
import NearCompression.PreparedLocalsSequential
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536

theorem prepared_locals_branch_opcode (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (branch : tr.cell t r 606=1) :
    (∀i,i<4 → tr.cell t r (466+i)=0) ∧ tr.cell t r 605=0 := by
  have ops:=(prepared_locals_control_opcode_exclusive count tr t r pub localH hr 5 (by decide) branch).1
  constructor
  · intro i hi
    simpa only [preparedControlOpcodeColumn,hi,ite_true,show ¬i=5 by omega,ite_false] using ops i (by omega)
  · exact ops 4 (by decide)

theorem prepared_locals_taken_pc (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1) :
    preparedCodeExecPC (tr.cell t (r+1))=preparedControlSavedTarget (tr.cell t r) := by
  have taken:=prepared_control_taken_eval tr t r pub active charged branch nonzero
  have limb (i : Nat) (hi : i<2) : preparedCodeLimb (tr.cell t (r+1)) (16*i)=
      preparedCodeLimb (tr.cell t r) (649+16*i) := by
    have member : preparedControlJump i∈(preparedLocalsLiteralExecTable count).constraints := by
      have cases : i=0 ∨ i=1:=by omega
      rcases cases with h|h <;> subst i
      · exact prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1006) (by decide))
      · exact prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1007) (by decide))
    have h:=localH.constr r (by omega) _ member
    change ((if r+1=tr.height t then (0:Fp) else 1)*preparedControlTaken.eval tr t r pub)*
      ((preparedCodeBits (16*i) true).eval tr t r pub+ -(preparedCodeBits (649+16*i)).eval tr t r pub)=0 at h
    rw [if_neg (by omega),taken,prepared_code_bits_eval,prepared_code_bits_eval] at h
    simp only [Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt nonlast] at h
    grind
  unfold preparedCodeExecPC preparedControlSavedTarget
  rw [limb 0 (by decide),limb 1 (by decide)]

theorem prepared_locals_taken_gates (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1) :
    preparedControlOpened.eval tr t r pub=0 ∧ preparedControlKeep.eval tr t r pub=0 := by
  have ops:=prepared_locals_branch_opcode count tr t r pub localH hr branch
  have opened : preparedControlOpened.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*tr.cell t r 605=0
    rw [ops.2];grind
  have taken:=prepared_control_taken_eval tr t r pub active charged branch nonzero
  refine ⟨opened,?_⟩
  change (1:Fp)+ -(preparedControlOpened.eval tr t r pub+
    (preparedControlTaken.eval tr t r pub+preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 469*tr.cell t r 639)))=0
  rw [opened,taken,ops.1 3 (by decide)];grind

private theorem control_height_at : ∀ i:Fin 9,
    preparedLocalsLiteralExecBase[1048+i.val]'(by change _<1144;omega)=preparedControlHeightStep i.val := by decide

/-- A successful taken branch discards the nested label and canonically
clears its saved height and target; failure and padding are not this case. -/
theorem prepared_locals_taken_label (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1) :
    tr.cell t (r+1) 639=0 ∧ (∀ i,i<9 → tr.cell t (r+1) (640+i)=0) ∧
    preparedControlSavedTarget (tr.cell t (r+1))=0 := by
  have gates:=prepared_locals_taken_gates count tr t r pub localH (by omega) active charged branch nonzero
  have trans : (if r+1=tr.height t then (0:Fp) else 1)=1:=if_neg (by omega)
  refine ⟨?_,?_,?_⟩
  · have member : preparedControlLabelStep∈(preparedLocalsLiteralExecTable count).constraints :=
      prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1047) (by decide))
    have h:=localH.constr r (by omega) _ member
    change (if r+1=tr.height t then (0:Fp) else 1)*(tr.cell t ((r+1)%tr.height t) 639+
      -(preparedControlOpened.eval tr t r pub+preparedControlKeep.eval tr t r pub*tr.cell t r 639))=0 at h
    rw [trans,gates.1,gates.2,Nat.mod_eq_of_lt nonlast] at h
    grind
  · intro i hi
    have member:=List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1048+i) (by change _<1144;omega)
    rw [control_height_at ⟨i,hi⟩] at member
    have h:=localH.constr r (by omega) _ (prepared_locals_base_member count _ member)
    change (if r+1=tr.height t then (0:Fp) else 1)*(tr.cell t ((r+1)%tr.height t) (640+i)+
      -(preparedControlOpened.eval tr t r pub*tr.cell t r (32+i)+preparedControlKeep.eval tr t r pub*tr.cell t r (640+i)))=0 at h
    rw [trans,gates.1,gates.2,Nat.mod_eq_of_lt nonlast] at h
    grind
  · have limb (i : Nat) (hi : i<2) : preparedCodeLimb (tr.cell t (r+1)) (649+16*i)=0 := by
      have member : preparedControlTargetStep i∈(preparedLocalsLiteralExecTable count).constraints := by
        have cases : i=0 ∨ i=1:=by omega
        rcases cases with h|h <;> subst i
        · exact prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1057) (by decide))
        · exact prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1059) (by decide))
      have h:=localH.constr r (by omega) _ member
      change (if r+1=tr.height t then (0:Fp) else 1)*((preparedCodeBits (649+16*i) true).eval tr t r pub+
        -(preparedControlOpened.eval tr t r pub*(preparedCodeBits (607+16*i)).eval tr t r pub+
          preparedControlKeep.eval tr t r pub*(preparedCodeBits (649+16*i)).eval tr t r pub))=0 at h
      rw [trans,gates.1,gates.2,prepared_code_bits_eval] at h
      simp only [ite_true,Nat.mod_eq_of_lt nonlast] at h
      grind
    unfold preparedControlSavedTarget
    rw [limb 0 (by decide),limb 1 (by decide)]
    rfl

end NearCompression
