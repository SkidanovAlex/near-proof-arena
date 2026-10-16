import NearCompression.PreparedTypedFrameStack
import NearCompression.PreparedTypedQuietControl
import NearCompression.PreparedTypedSequential
import NearCompression.PreparedTypedLocalPreserve
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem sp_at : ∀count:Fin 5,
    (preparedTypedLiteralExec count)[1661+66*(4-count.val)]?=some preparedTypedQuietSPStep := by decide

theorem prepared_typed_frame_depth (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (tag : Nat) (which : tag=3 ∨ tag=4) (opcode : tr.cell t r (preparedTypedOpcodeColumn tag)=1)
    (sp : Nat) (bound : sp<9) (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    ∀i,i<9 → tr.cell t (r+1) (32+i)=if i=sp then 1 else 0 := by
  obtain ⟨next,nb,nh⟩:=prepared_typed_source_sp count hc tr t (r+1) pub localH nonlast
  have h:=localH.constr r (by omega) _ (List.mem_of_getElem? (sp_at ⟨count,by omega⟩))
  have flags:=prepared_typed_opcode_selected count hc tr t r pub localH (by omega) tag (by omega) opcode
  have z0 : tr.cell t r 466=0 := by
    have h:=flags 0 (by decide)
    change tr.cell t r 466=(if 0=tag then 1 else 0) at h
    simpa only [show ¬0=tag by omega,ite_false] using h
  have z1 : tr.cell t r 467=0 := by
    have h:=flags 1 (by decide)
    change tr.cell t r 467=(if 1=tag then 1 else 0) at h
    simpa only [show ¬1=tag by omega,ite_false] using h
  have z2 : tr.cell t r 468=0 := by
    have h:=flags 2 (by decide)
    change tr.cell t r 468=(if 2=tag then 1 else 0) at h
    simpa only [show ¬2=tag by omega,ite_false] using h
  have z5 : tr.cell t r 606=0 := by
    have h:=flags 5 (by decide)
    change tr.cell t r 606=(if 5=tag then 1 else 0) at h
    simpa only [show ¬5=tag by omega,ite_false] using h
  have z6 : tr.cell t r 683=0 := by
    have h:=flags 6 (by decide)
    change tr.cell t r 683=(if 6=tag then 1 else 0) at h
    simpa only [show ¬6=tag by omega,ite_false] using h
  have z7 : tr.cell t r 684=0 := by
    have h:=flags 7 (by decide)
    change tr.cell t r 684=(if 7=tag then 1 else 0) at h
    simpa only [show ¬7=tag by omega,ite_false] using h
  have z9 : tr.cell t r 1280=0 := by
    have h:=flags 9 (by decide)
    change tr.cell t r 1280=(if 9=tag then 1 else 0) at h
    simpa only [show ¬9=tag by omega,ite_false] using h
  have z10 : tr.cell t r 1281=0 := by
    have h:=flags 10 (by decide)
    change tr.cell t r 1281=(if 10=tag then 1 else 0) at h
    simpa only [show ¬10=tag by omega,ite_false] using h
  have delta : preparedTypedQuietDelta.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*
      (tr.cell t r 466+tr.cell t r 1280+tr.cell t r 683+ -((tr.cell t r 467+tr.cell t r 1281+tr.cell t r 468+tr.cell t r 606)+tr.cell t r 684))=0
    rw [z0,z1,z2,z5,z6,z7,z9,z10];grind
  have taken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [z5];grind
  change (if r+1=tr.height t then (0:Fp) else 1)*((preparedControlIndex 32 true).eval tr t r pub+
    -(preparedControlTaken.eval tr t r pub*(preparedControlIndex 640).eval tr t r pub+
      ((1:Fp)+ -preparedControlTaken.eval tr t r pub)*((preparedControlIndex 32).eval tr t r pub+preparedTypedQuietDelta.eval tr t r pub)))=0 at h
  have current : (preparedControlIndex 32).eval tr t r pub=Fp.ofNat sp := prepared_control_index_selected (tr.cell t r) 32 sp bound hot
  have following : (preparedControlIndex 32 true).eval tr t r pub=Fp.ofNat next := by
    have eq:=prepared_control_index_selected (tr.cell t (r+1)) 32 next nb nh
    simpa only [preparedControlIndex,preparedBalancedSum,Expr.eval,Expr.evalWith,rowEnv,instructionAddEnv,ite_true,
      Nat.mod_eq_of_lt nonlast,←Lean.Grind.Semiring.ofNat_eq_natCast,←Fp.ofNat_def] using eq
  rw [if_neg (by omega),taken,delta,current,following] at h
  have eq : Fp.ofNat next=Fp.ofNat sp:=by grind
  have natural:=congrArg Fp.toNat eq
  simp only [Fp.toNat_ofNat] at natural
  rw [Nat.mod_eq_of_lt (show next<ZkFormal.Algebra.P by unfold ZkFormal.Algebra.P;omega),
    Nat.mod_eq_of_lt (show sp<ZkFormal.Algebra.P by unfold ZkFormal.Algebra.P;omega)] at natural
  simpa only [natural] using nh

end NearCompression
