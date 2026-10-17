import NearCompression.PreparedLocalsQuiet
import NearCompression.PreparedLocalsAuthenticated
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536

theorem prepared_locals_padding_step (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr) (r : Nat) (nonlast : r+1<tr.height 0)
    (done : tr.cell 0 r 41=1) : PreparedExecSnapshotEq (tr.cell 0 r) (tr.cell 0 (r+1)) := by
  have localH:=prepared_locals_exec_local codeCount count tr pub holds
  have success : preparedExecGasSuccess.eval tr 0 r pub=0 := by
    change ((1:Fp)+ -tr.cell 0 r 41)*_=0
    rw [done];grind
  have advance : preparedControlAdvance.eval tr 0 r pub=0 := by
    change preparedExecGasSuccess.eval tr 0 r pub*_=0
    rw [success];grind
  have q:=prepared_locals_quiet count tr 0 r pub localH nonlast success
  have nextDone:=localH.constr r (by omega) preparedLocalsLiteralExec1002
    (prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1002) (by decide)))
  have nextFail:=localH.constr r (by omega) preparedLocalsLiteralExec1003
    (prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1003) (by decide)))
  change (if r+1=tr.height 0 then (0:Fp) else 1)*(tr.cell 0 ((r+1)%tr.height 0) 41+
    -(tr.cell 0 r 41+(((1:Fp)+ -tr.cell 0 r 41)*tr.cell 0 r 430+
      (((1:Fp)+ -tr.cell 0 r 41)*((1:Fp)+ -tr.cell 0 r 430))*(tr.cell 0 r 469*((1:Fp)+ -tr.cell 0 r 639)))))=0 at nextDone
  change (if r+1=tr.height 0 then (0:Fp) else 1)*(tr.cell 0 ((r+1)%tr.height 0) 42+
    -(tr.cell 0 r 42+((1:Fp)+ -tr.cell 0 r 41)*tr.cell 0 r 430))=0 at nextFail
  rw [if_neg (by omega),Nat.mod_eq_of_lt nonlast,done] at nextDone nextFail
  refine ⟨by rw [done];grind,by grind,?_,q⟩
  exact prepared_control_gas_update_word _ tr 0 r pub (prepared_locals_gas_source count) localH nonlast false success

theorem prepared_locals_padding_suffix (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr) (r : Nat) (done : tr.cell 0 r 41=1)
    (distance : Nat) (bound : r+distance<tr.height 0) :
    PreparedExecSnapshotEq (tr.cell 0 r) (tr.cell 0 (r+distance)) := by
  induction distance with
  | zero => exact ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
  | succ distance ih =>
    have previous:=ih (by omega)
    have step:=prepared_locals_padding_step codeCount count tr pub holds (r+distance) (by omega) (previous.1.trans done)
    exact prepared_exec_snapshot_trans _ _ _ previous step

end NearCompression
