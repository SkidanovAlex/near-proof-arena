import NearCompression.PreparedTypedOpcode
import NearCompression.PreparedTypedEqzGuard
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
def preparedTypedDelta : Expr :=
  .mul preparedExecGasSuccess (.add (.add (.add (.col 466 false) (.col 1280 false)) (.col 683 false))
    (.neg (.add (.add (.add (.add (.col 467 false) (.col 1281 false)) (.col 468 false)) (.col 606 false)) (.col 684 false))))
def preparedTypedSPStep : Expr :=
  .mul .isTransition (.add (preparedControlIndex 32 true)
    (.neg (.add (.mul preparedControlTaken (preparedControlIndex 640))
      (.mul (.add (.const 1) (.neg preparedControlTaken))
        (.add (preparedControlIndex 32) preparedTypedDelta)))))
private theorem sp_at : ∀count:Fin 5,
    (preparedTypedLiteralExec count)[1661+66*(4-count.val)]?=some preparedTypedSPStep := by decide

theorem prepared_typed_eqz_depth (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (opcode : tr.cell t r 1282=1)
    (sp : Nat) (bound : sp<9) (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    ∀i,i<9 → tr.cell t (r+1) (32+i)=if i=sp then 1 else 0 := by
  obtain ⟨next,nb,nh⟩:=prepared_typed_source_sp count hc tr t (r+1) pub localH nonlast
  have h:=localH.constr r (by omega) _ (List.mem_of_getElem? (sp_at ⟨count,by omega⟩))
  have flags:=prepared_typed_opcode_selected count hc tr t r pub localH (by omega) 11 (by decide) opcode
  have f0:=flags 0 (by decide);have f1:=flags 1 (by decide);have f2:=flags 2 (by decide)
  have f5:=flags 5 (by decide);have f6:=flags 6 (by decide);have f7:=flags 7 (by decide)
  have f9:=flags 9 (by decide);have f10:=flags 10 (by decide)
  change tr.cell t r 466=0 at f0
  change tr.cell t r 467=0 at f1
  change tr.cell t r 468=0 at f2
  change tr.cell t r 606=0 at f5
  change tr.cell t r 683=0 at f6
  change tr.cell t r 684=0 at f7
  change tr.cell t r 1280=0 at f9
  change tr.cell t r 1281=0 at f10
  have delta : preparedTypedDelta.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*((tr.cell t r 466+tr.cell t r 1280+tr.cell t r 683)+
      -(tr.cell t r 467+tr.cell t r 1281+tr.cell t r 468+tr.cell t r 606+tr.cell t r 684))=0
    rw [f0,f1,f2,f5,f6,f7,f9,f10];grind
  have taken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [f5];grind
  change (if r+1=tr.height t then (0:Fp) else 1)*((preparedControlIndex 32 true).eval tr t r pub+
    -(preparedControlTaken.eval tr t r pub*(preparedControlIndex 640).eval tr t r pub+
      ((1:Fp)+ -preparedControlTaken.eval tr t r pub)*((preparedControlIndex 32).eval tr t r pub+preparedTypedDelta.eval tr t r pub)))=0 at h
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
