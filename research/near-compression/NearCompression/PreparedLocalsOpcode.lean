import NearCompression.PreparedLocalsUpdate
import NearCompression.PreparedControlBlock
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536

def preparedLocalsOpcodeColumn (i : Nat) : Nat :=
  if i<6 then preparedControlOpcodeColumn i else 683+(i-6)

theorem prepared_locals_opcode_selected (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (hr : r<tr.height t) :
    ∃tag,tag<9 ∧ ∀i,i<9 → tr.cell t r (preparedLocalsOpcodeColumn i)=if i=tag then 1 else 0 := by
  suffices h : ∃tag,tag<9 ∧ ∀i,i<9 → tr.cell t r (preparedLocalsOpcodeColumn (0+i))=if i=tag then 1 else 0 by
    simpa only [Nat.zero_add] using h
  apply prepared_onehot 9 0 (fun i=>tr.cell t r (preparedLocalsOpcodeColumn i)) (by decide)
  · intro i hi
    simp only [Nat.zero_add]
    apply prepared_locals_bits_boolean count tr t r pub localH hr
    · unfold preparedLocalsOpcodeColumn preparedControlOpcodeColumn
      split <;> first | split <;> omega | omega
    · unfold preparedLocalsOpcodeColumn preparedControlOpcodeColumn
      split <;> first | split <;> omega | omega
  · have h:=localH.constr r hr _ (prepared_locals_base_member count _
      (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=820) (by decide)))
    change (((tr.cell t r 466+tr.cell t r 467)+(tr.cell t r 468+tr.cell t r 469))+
      ((tr.cell t r 605+tr.cell t r 606)+(tr.cell t r 683+tr.cell t r 684))+tr.cell t r 685)+ -(1:Fp)=0 at h
    simp only [preparedFieldSum,preparedLocalsOpcodeColumn,preparedControlOpcodeColumn,
      Nat.reduceAdd,Nat.reduceLT,Nat.reduceSub,ite_true,ite_false]
    grind

theorem prepared_locals_opcode_exclusive (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (wanted : Nat) (bound : wanted<9) (one : tr.cell t r (preparedLocalsOpcodeColumn wanted)=1) :
    ∀i,i<9 → tr.cell t r (preparedLocalsOpcodeColumn i)=if i=wanted then 1 else 0 := by
  obtain ⟨tag,tb,ops⟩:=prepared_locals_opcode_selected count tr t r pub localH hr
  have atWanted:=ops wanted bound
  rw [one] at atWanted
  have same : wanted=tag := by
    by_cases eq:wanted=tag
    · exact eq
    · rw [ite_eq_right eq] at atWanted
      exact False.elim ((by decide : (1:Fp)≠0) atWanted)
  exact same.symm ▸ ops

/-- The inherited six-tag interface follows from the actual nine-tag AIR. -/
theorem prepared_locals_control_opcode_exclusive (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (wanted : Nat) (bound : wanted<6) (one : tr.cell t r (preparedControlOpcodeColumn wanted)=1) :
    (∀i,i<6 → tr.cell t r (preparedControlOpcodeColumn i)=if i=wanted then 1 else 0) ∧
    ∀i,i<3 → tr.cell t r (683+i)=0 := by
  have ops:=prepared_locals_opcode_exclusive count tr t r pub localH hr wanted (by omega)
    (by simpa only [preparedLocalsOpcodeColumn,bound,ite_true] using one)
  constructor
  · intro i hi
    simpa only [preparedLocalsOpcodeColumn,hi,ite_true] using ops i (by omega)
  · intro i hi
    have h:=ops (6+i) (by omega)
    simpa only [preparedLocalsOpcodeColumn,show ¬6+i<6 by omega,ite_false,
      show 6+i-6=i by omega,show ¬6+i=wanted by omega] using h
end NearCompression
