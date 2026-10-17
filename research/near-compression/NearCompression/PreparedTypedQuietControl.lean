import NearCompression.PreparedTypedOpcode
import NearCompression.PreparedTypedSequential
import NearCompression.PreparedTypedLocalPreserve
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
def preparedTypedQuietDelta : Expr :=
  .mul preparedExecGasSuccess (.add (.add (.add (.col 466 false) (.col 1280 false)) (.col 683 false))
    (.neg (.add (.add (.add (.add (.col 467 false) (.col 1281 false)) (.col 468 false)) (.col 606 false)) (.col 684 false))))
def preparedTypedQuietSPStep : Expr :=
  .mul .isTransition (.add (preparedControlIndex 32 true)
    (.neg (.add (.mul preparedControlTaken (preparedControlIndex 640))
      (.mul (.add (.const 1) (.neg preparedControlTaken))
        (.add (preparedControlIndex 32) preparedTypedQuietDelta)))))
private theorem sp_at : ∀count:Fin 5,
    (preparedTypedLiteralExec count)[1661+66*(4-count.val)]?=some preparedTypedQuietSPStep := by decide

theorem prepared_typed_quiet_depth (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (quiet : preparedExecGasSuccess.eval tr t r pub=0)
    (sp : Nat) (bound : sp<9) (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    ∀i,i<9 → tr.cell t (r+1) (32+i)=if i=sp then 1 else 0 := by
  obtain ⟨next,nb,nh⟩:=prepared_typed_source_sp count hc tr t (r+1) pub localH nonlast
  have h:=localH.constr r (by omega) _ (List.mem_of_getElem? (sp_at ⟨count,by omega⟩))
  have delta : preparedTypedQuietDelta.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*_=0
    rw [quiet];grind
  have taken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [quiet];grind
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
theorem prepared_typed_quiet_pc_labels (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (quiet : preparedExecGasSuccess.eval tr t r pub=0) :
    preparedCodeExecPC (tr.cell t (r+1))=preparedCodeExecPC (tr.cell t r) ∧
    tr.cell t (r+1) 639=tr.cell t r 639 ∧
    (∀i,i<9 → tr.cell t (r+1) (640+i)=tr.cell t r (640+i)) ∧
    preparedControlSavedTarget (tr.cell t (r+1))=preparedControlSavedTarget (tr.cell t r) := by
  have taken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*_=0;rw [quiet];grind
  have advance : preparedControlAdvance.eval tr t r pub=Fp.ofNat 0 := by
    change preparedExecGasSuccess.eval tr t r pub*_=0;rw [quiet];grind
  have opened : preparedControlOpened.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*_=0;rw [quiet];grind
  have keep : preparedControlKeep.eval tr t r pub=1 := by
    change (1:Fp)+ -(preparedControlOpened.eval tr t r pub+
      (preparedControlTaken.eval tr t r pub+preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 469*tr.cell t r 639)))=1
    rw [opened,taken,quiet];grind
  have pc:=prepared_typed_sequential_pc count hc tr t r pub localH nonlast taken 0 (by decide) advance
  have labels:=prepared_typed_label_equations count hc tr t r pub localH nonlast
  rw [opened,keep] at labels
  refine ⟨by simpa using pc,by grind,?_,?_⟩
  · intro i hi;have h:=labels.2.1 i hi;grind
  · have low:=labels.2.2 0 (by decide)
    have high:=labels.2.2 1 (by decide)
    have l : preparedCodeLimb (tr.cell t (r+1)) 649=preparedCodeLimb (tr.cell t r) 649:=by simpa only [Nat.mul_zero,Nat.add_zero] using (show _=_ from by grind)
    have h : preparedCodeLimb (tr.cell t (r+1)) 665=preparedCodeLimb (tr.cell t r) 665:=by simpa only [Nat.mul_one,Nat.reduceAdd] using (show _=_ from by grind)
    unfold preparedControlSavedTarget
    rw [l,h]

end NearCompression
