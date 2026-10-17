import NearCompression.PreparedTypedBranch
import NearCompression.PreparedTypedQuietControl
import NearCompression.PreparedTypedSequential
import NearCompression.PreparedTypedLocalPreserve
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem sp_at : ∀count:Fin 5,
    (preparedTypedLiteralExec count)[1661+66*(4-count.val)]?=some preparedTypedQuietSPStep := by decide

theorem prepared_typed_branch_depth (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (opcode : tr.cell t r 606=1)
    (taken : Bool) (flag : tr.cell t r 681=if taken then 1 else 0)
    (height : Nat) (hb : height<9) (saved : ∀i,i<9 → tr.cell t r (640+i)=if i=height then 1 else 0)
    (sp : Nat) (bound : sp<9) (positive : 0<sp) (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    ∀i,i<9 → tr.cell t (r+1) (32+i)=if i=(if taken then height else sp-1) then 1 else 0 := by
  obtain ⟨next,nb,nh⟩:=prepared_typed_source_sp count hc tr t (r+1) pub localH nonlast
  have h:=localH.constr r (by omega) _ (List.mem_of_getElem? (sp_at ⟨count,by omega⟩))
  have flags:=prepared_typed_opcode_selected count hc tr t r pub localH (by omega) 5 (by decide) opcode
  have z0 : tr.cell t r 466=0 := by
    have h:=flags 0 (by decide)
    change tr.cell t r 466=(if 0=5 then 1 else 0) at h
    simpa only [show ¬0=5 by decide,ite_false] using h
  have z1 : tr.cell t r 467=0 := by
    have h:=flags 1 (by decide)
    change tr.cell t r 467=(if 1=5 then 1 else 0) at h
    simpa only [show ¬1=5 by decide,ite_false] using h
  have z2 : tr.cell t r 468=0 := by
    have h:=flags 2 (by decide)
    change tr.cell t r 468=(if 2=5 then 1 else 0) at h
    simpa only [show ¬2=5 by decide,ite_false] using h
  have z6 : tr.cell t r 683=0 := by
    have h:=flags 6 (by decide)
    change tr.cell t r 683=(if 6=5 then 1 else 0) at h
    simpa only [show ¬6=5 by decide,ite_false] using h
  have z7 : tr.cell t r 684=0 := by
    have h:=flags 7 (by decide)
    change tr.cell t r 684=(if 7=5 then 1 else 0) at h
    simpa only [show ¬7=5 by decide,ite_false] using h
  have z9 : tr.cell t r 1280=0 := by
    have h:=flags 9 (by decide)
    change tr.cell t r 1280=(if 9=5 then 1 else 0) at h
    simpa only [show ¬9=5 by decide,ite_false] using h
  have z10 : tr.cell t r 1281=0 := by
    have h:=flags 10 (by decide)
    change tr.cell t r 1281=(if 10=5 then 1 else 0) at h
    simpa only [show ¬10=5 by decide,ite_false] using h
  have delta : preparedTypedQuietDelta.eval tr t r pub= -(1:Fp) := by
    change preparedExecGasSuccess.eval tr t r pub*
      (tr.cell t r 466+tr.cell t r 1280+tr.cell t r 683+ -((tr.cell t r 467+tr.cell t r 1281+tr.cell t r 468+tr.cell t r 606)+tr.cell t r 684))= -(1:Fp)
    rw [z0,z1,z2,opcode,z6,z7,z9,z10]
    change ((1+ -tr.cell t r 41)*(1+ -tr.cell t r 430))*_= -1
    rw [active,charged];grind
  have takenEq : preparedControlTaken.eval tr t r pub=(if taken then 1 else 0) := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=(if taken then 1 else 0)
    rw [opcode,flag]
    change ((1+ -tr.cell t r 41)*(1+ -tr.cell t r 430))*_=_
    rw [active,charged];grind
  change (if r+1=tr.height t then (0:Fp) else 1)*((preparedControlIndex 32 true).eval tr t r pub+
    -(preparedControlTaken.eval tr t r pub*(preparedControlIndex 640).eval tr t r pub+
      ((1:Fp)+ -preparedControlTaken.eval tr t r pub)*((preparedControlIndex 32).eval tr t r pub+preparedTypedQuietDelta.eval tr t r pub)))=0 at h
  have current : (preparedControlIndex 32).eval tr t r pub=Fp.ofNat sp := prepared_control_index_selected (tr.cell t r) 32 sp bound hot
  have following : (preparedControlIndex 32 true).eval tr t r pub=Fp.ofNat next := by
    have eq:=prepared_control_index_selected (tr.cell t (r+1)) 32 next nb nh
    simpa only [preparedControlIndex,preparedBalancedSum,Expr.eval,Expr.evalWith,rowEnv,instructionAddEnv,ite_true,
      Nat.mod_eq_of_lt nonlast,←Lean.Grind.Semiring.ofNat_eq_natCast,←Fp.ofNat_def] using eq
  have savedEq : (preparedControlIndex 640).eval tr t r pub=Fp.ofNat height:=prepared_control_index_selected (tr.cell t r) 640 height hb saved
  rw [if_neg (by omega),takenEq,delta,current,following,savedEq] at h
  cases taken with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at h ⊢
    have eq : Fp.ofNat next+1=Fp.ofNat sp:=by grind
    have natural:=congrArg Fp.toNat eq
    change (Fp.add (Fp.ofNat next) (Fp.ofNat 1)).toNat=(Fp.ofNat sp).toNat at natural
    simp only [Fp.toNat_add,Fp.toNat_ofNat] at natural
    change (next%ZkFormal.Algebra.P+1)%ZkFormal.Algebra.P=sp%ZkFormal.Algebra.P at natural
    rw [Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega),Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega),
      Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega)] at natural
    have e:next=sp-1:=by omega
    simpa only [e] using nh
  | true =>
    simp only [ite_true] at h ⊢
    have eq : Fp.ofNat next=Fp.ofNat height:=by grind
    have natural:=congrArg Fp.toNat eq
    simp only [Fp.toNat_ofNat] at natural
    rw [Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega),Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega)] at natural
    simpa only [natural] using nh
end NearCompression
