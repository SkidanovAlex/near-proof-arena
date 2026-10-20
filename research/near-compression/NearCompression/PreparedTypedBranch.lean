import NearCompression.PreparedTypedSequential
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
private theorem jump_at : ∀count:Fin 5,∀i:Fin 2,(preparedTypedLiteralExec count)[1627+66*(4-count.val)+i.val]?=some (preparedControlJump i) := by decide

theorem prepared_typed_branch_opcode (count : Nat) (hc : count≤4) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (branch : tr.cell t r 606=1) :
    (∀i,i<4 → tr.cell t r (466+i)=0) ∧ tr.cell t r 605=0 := by
  have ops:=prepared_typed_opcode_selected count hc tr t r pub localH hr 5 (by decide) branch
  constructor
  · intro i hi
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3:=by omega
    rcases cases with rfl|rfl|rfl|rfl
    · exact ops 0 (by decide)
    · exact ops 1 (by decide)
    · exact ops 2 (by decide)
    · exact ops 3 (by decide)
  · exact ops 4 (by decide)

theorem prepared_typed_taken_pc (count : Nat) (hc : count≤4) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1) :
    preparedCodeExecPC (tr.cell t (r+1))=preparedControlSavedTarget (tr.cell t r) := by
  have taken:=prepared_control_taken_eval tr t r pub active charged branch nonzero
  have limb (i : Nat) (hi : i<2) : preparedCodeLimb (tr.cell t (r+1)) (16*i)=
      preparedCodeLimb (tr.cell t r) (649+16*i) := by
    have member : preparedControlJump i∈(preparedTypedLiteralExecTable count).constraints := by
      have cases : i=0 ∨ i=1:=by omega
      rcases cases with h|h <;> subst i
      · exact List.mem_of_getElem? (jump_at ⟨count,by omega⟩ 0)
      · exact List.mem_of_getElem? (jump_at ⟨count,by omega⟩ 1)
    have h:=localH.constr r (by omega) _ member
    change ((if r+1=tr.height t then (0:Fp) else 1)*preparedControlTaken.eval tr t r pub)*
      ((preparedCodeBits (16*i) true).eval tr t r pub+ -(preparedCodeBits (649+16*i)).eval tr t r pub)=0 at h
    rw [if_neg (by omega),taken,prepared_code_bits_eval,prepared_code_bits_eval] at h
    simp only [Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt nonlast] at h
    grind
  unfold preparedCodeExecPC preparedControlSavedTarget
  rw [limb 0 (by decide),limb 1 (by decide)]

theorem prepared_typed_taken_gates (count : Nat) (hc : count≤4) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1) :
    preparedControlOpened.eval tr t r pub=0 ∧ preparedControlKeep.eval tr t r pub=0 := by
  have ops:=prepared_typed_branch_opcode count hc tr t r pub localH hr branch
  have opened : preparedControlOpened.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*tr.cell t r 605=0
    rw [ops.2];grind
  have taken:=prepared_control_taken_eval tr t r pub active charged branch nonzero
  refine ⟨opened,?_⟩
  change (1:Fp)+ -(preparedControlOpened.eval tr t r pub+
    (preparedControlTaken.eval tr t r pub+preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 469*tr.cell t r 639)))=0
  rw [opened,taken,ops.1 3 (by decide)];grind

theorem prepared_typed_taken_label (count : Nat) (hc : count≤4) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1) :
    tr.cell t (r+1) 639=0 ∧ (∀i,i<9 → tr.cell t (r+1) (640+i)=0) ∧
    preparedControlSavedTarget (tr.cell t (r+1))=0 := by
  have gates:=prepared_typed_taken_gates count hc tr t r pub localH (by omega) active charged branch nonzero
  have eq:=prepared_typed_label_equations count hc tr t r pub localH nonlast
  rw [gates.1,gates.2] at eq
  refine ⟨by grind,?_,?_⟩
  · intro i hi;have h:=eq.2.1 i hi;grind
  · have lo:=eq.2.2 0 (by decide);have hi:=eq.2.2 1 (by decide)
    have l:preparedCodeLimb (tr.cell t (r+1)) 649=0:=by grind
    have h:preparedCodeLimb (tr.cell t (r+1)) 665=0:=by grind
    unfold preparedControlSavedTarget
    rw [l,h];rfl
end NearCompression
