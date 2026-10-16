import NearCompression.PreparedLocalsUpdate
import NearCompression.PreparedControlStack
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536

def preparedLocalsDelta : Expr :=
  .mul preparedExecGasSuccess (.add (.add (.col 466 false) (.col 683 false))
    (.neg (.add (.add (.add (.col 467 false) (.col 468 false)) (.col 606 false)) (.col 684 false))))
def preparedLocalsSPStep : Expr :=
  .mul .isTransition (.add (preparedControlIndex 32 true)
    (.neg (.add (.mul preparedControlTaken (preparedControlIndex 640))
      (.mul (.add (.const 1) (.neg preparedControlTaken))
        (.add (preparedControlIndex 32) preparedLocalsDelta)))))

theorem prepared_locals_onehot (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (hr : r<tr.height t) :
    ∃ sp,sp<9 ∧ ∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0 := by
  apply prepared_onehot 9 32 (tr.cell t r) (by decide)
  · intro i hi
    exact prepared_locals_bits_boolean count tr t r pub localH hr (32+i) (by omega) (by omega)
  · have member : preparedExecSPChoice∈(preparedLocalsLiteralExecTable count).constraints:=
      prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=817) (by decide))
    have h:=localH.constr r hr _ member
    simp only [preparedExecSPChoice,preparedBalancedSum,Expr.eval,Expr.evalWith,rowEnv,
      Nat.reduceAdd,Nat.reducePow,Bool.false_eq_true,ite_false] at h
    simp only [preparedFieldSum,Nat.reduceAdd]
    try simp only [←Fp.ofNat_def] at h
    grind

/-- Natural stack-depth update, with no field-wrap interpretation. The local
opcode flags and active/charged status remain explicit for composition. -/
theorem prepared_locals_depth_step (kind : PreparedLocalOp) (count : Nat)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (nonlast : r+1<tr.height t) (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (old : ∀i,i<3 → tr.cell t r (466+i)=0) (branch : tr.cell t r 606=0)
    (get : tr.cell t r 683=if kind=.get then 1 else 0)
    (set : tr.cell t r 684=if kind=.set then 1 else 0)
    (tee : tr.cell t r 685=if kind=.tee then 1 else 0)
    (sp : Nat) (bound : sp<9) (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    (if kind=.get then sp<8 else 0<sp) ∧
    ∃ next,next<9 ∧ next+(if kind=.set then 1 else 0)=sp+(if kind=.get then 1 else 0) ∧
      ∀i,i<9 → tr.cell t (r+1) (32+i)=if i=next then 1 else 0 := by
  obtain ⟨next,nb,nh⟩:=prepared_locals_onehot count tr t (r+1) pub localH nonlast
  have member : preparedLocalsSPStep∈(preparedLocalsLiteralExecTable count).constraints :=
    prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1040) (by decide))
  have h:=localH.constr r (by omega) _ member
  change (if r+1=tr.height t then (0:Fp) else 1)*((preparedControlIndex 32 true).eval tr t r pub+
    -(preparedControlTaken.eval tr t r pub*(preparedControlIndex 640).eval tr t r pub+
      ((1:Fp)+ -preparedControlTaken.eval tr t r pub)*((preparedControlIndex 32).eval tr t r pub+preparedLocalsDelta.eval tr t r pub)))=0 at h
  have noTaken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [branch];grind
  have delta : preparedLocalsDelta.eval tr t r pub=
      (if kind=.get then (1:Fp) else 0) - (if kind=.set then 1 else 0) := by
    change (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*
      (tr.cell t r 466+tr.cell t r 683+ -((tr.cell t r 467+tr.cell t r 468+tr.cell t r 606)+tr.cell t r 684))=_
    rw [active,charged,old 0 (by decide),old 1 (by decide),old 2 (by decide),branch,get,set]
    grind
  have current : (preparedControlIndex 32).eval tr t r pub=Fp.ofNat sp :=
    prepared_control_index_selected (tr.cell t r) 32 sp bound hot
  have following : (preparedControlIndex 32 true).eval tr t r pub=Fp.ofNat next := by
    have eq:=prepared_control_index_selected (tr.cell t (r+1)) 32 next nb nh
    simpa only [preparedControlIndex,preparedBalancedSum,Expr.eval,Expr.evalWith,rowEnv,
      instructionAddEnv,ite_true,Nat.mod_eq_of_lt nonlast,←Lean.Grind.Semiring.ofNat_eq_natCast,←Fp.ofNat_def] using eq
  rw [ite_eq_right (by omega),noTaken,delta,current,following] at h
  have succ (n : Nat) : Fp.ofNat (n+1)=Fp.ofNat n+1 := by
    change ((n+1 : Nat) : Fp)=(n : Fp)+1
    rw [Lean.Grind.Semiring.natCast_add]
    rfl
  have relation : Fp.ofNat (next+(if kind=.set then 1 else 0))=
      Fp.ofNat (sp+(if kind=.get then 1 else 0)) := by
    cases kind <;> simp only [reduceCtorEq,ite_true,ite_false,Nat.add_zero,succ] at h ⊢ <;> grind
  have natural:=congrArg Fp.toNat relation
  simp only [Fp.toNat_ofNat] at natural
  have leftBound : next+(if kind=.set then 1 else 0)<ZkFormal.Algebra.P := by unfold ZkFormal.Algebra.P;split <;> omega
  have rightBound : sp+(if kind=.get then 1 else 0)<ZkFormal.Algebra.P := by unfold ZkFormal.Algebra.P;split <;> omega
  rw [Nat.mod_eq_of_lt leftBound,Nat.mod_eq_of_lt rightBound] at natural
  refine ⟨?_,next,nb,natural,nh⟩
  cases kind with
  | get => simp only [ite_true];simp only [reduceCtorEq,ite_true,ite_false,Nat.add_zero] at natural;omega
  | set => simp only [reduceCtorEq,ite_false];simp only [reduceCtorEq,ite_true,ite_false,Nat.add_zero] at natural;omega
  | tee =>
    simp only [reduceCtorEq,ite_false]
    have member : preparedLocalsLiteralExec1043∈(preparedLocalsLiteralExecTable count).constraints:=
      prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1043) (by decide))
    have guard:=localH.constr r (by omega) _ member
    change (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*
      ((tr.cell t r 468+tr.cell t r 606+(tr.cell t r 684+tr.cell t r 685))*tr.cell t r 32)+ -(0:Fp)=0 at guard
    rw [active,charged,old 2 (by decide),branch,set,tee] at guard
    have h0:=hot 0 (by decide)
    by_cases eq : sp=0
    · rw [eq] at h0
      simp only [Nat.add_zero,ite_true] at h0
      rw [h0] at guard
      have bad : (1:Fp)=0 := by
        simp only [reduceCtorEq,ite_true,ite_false] at guard
        grind
      exact False.elim ((by decide : (1:Fp)≠0) bad)
    · omega
end NearCompression
