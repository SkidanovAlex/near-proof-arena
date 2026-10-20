import NearCompression.PreparedControlQuiet
import NearCompression.PreparedControlAuthenticated
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536

theorem prepared_control_padding_step (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr) (r : Nat) (nonlast : r+1<tr.height 0)
    (done : tr.cell 0 r 41=1) : PreparedExecSnapshotEq (tr.cell 0 r) (tr.cell 0 (r+1)) := by
  have localH:=prepared_control_exec_local count tr pub holds
  have success : preparedExecGasSuccess.eval tr 0 r pub=0 := by
    change ((1:Fp)+ -tr.cell 0 r 41)*_=0
    rw [done];grind
  have advance : preparedControlAdvance.eval tr 0 r pub=0 := by
    change preparedExecGasSuccess.eval tr 0 r pub*_=0
    rw [success];grind
  have q:=prepared_control_quiet tr 0 r pub localH nonlast advance (by intro i hi;rw [success];grind)
  have nextDone:=localH.constr r (by omega) preparedControlLiteralExec0728
    (List.getElem_mem (l:=preparedControlLiteralExec) (n:=728) (by decide))
  have nextFail:=localH.constr r (by omega) preparedControlLiteralExec0729
    (List.getElem_mem (l:=preparedControlLiteralExec) (n:=729) (by decide))
  change (if r+1=tr.height 0 then (0:Fp) else 1)*(tr.cell 0 ((r+1)%tr.height 0) 41+
    -(tr.cell 0 r 41+(((1:Fp)+ -tr.cell 0 r 41)*tr.cell 0 r 430+
      (((1:Fp)+ -tr.cell 0 r 41)*((1:Fp)+ -tr.cell 0 r 430))*(tr.cell 0 r 469*((1:Fp)+ -tr.cell 0 r 639)))))=0 at nextDone
  change (if r+1=tr.height 0 then (0:Fp) else 1)*(tr.cell 0 ((r+1)%tr.height 0) 42+
    -(tr.cell 0 r 42+((1:Fp)+ -tr.cell 0 r 41)*tr.cell 0 r 430))=0 at nextFail
  rw [if_neg (by omega),Nat.mod_eq_of_lt nonlast,done] at nextDone nextFail
  refine ⟨by rw [done];grind,by grind,?_,q⟩
  exact prepared_control_gas_update_word _ tr 0 r pub prepared_control_literal_gas_source localH nonlast false success

theorem prepared_control_padding_suffix (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr) (r : Nat) (done : tr.cell 0 r 41=1)
    (distance : Nat) (bound : r+distance<tr.height 0) :
    PreparedExecSnapshotEq (tr.cell 0 r) (tr.cell 0 (r+distance)) := by
  induction distance with
  | zero => exact ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
  | succ distance ih =>
    have previous:=ih (by omega)
    have step:=prepared_control_padding_step count tr pub holds (r+distance) (by omega) (previous.1.trans done)
    exact prepared_exec_snapshot_trans _ _ _ previous step

end NearCompression
