import NearCompression.PreparedControlCondition

set_option maxRecDepth 65536
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm

def preparedControlTaken : Expr := .mul preparedExecGasSuccess (.mul (.col 606 false) (.col 681 false))
def preparedControlOpened : Expr := .mul preparedExecGasSuccess (.col 605 false)
def preparedControlClosed : Expr :=
  .add preparedControlTaken (.mul preparedExecGasSuccess (.mul (.col 469 false) (.col 639 false)))
def preparedControlKeep : Expr := .add (.const 1) (.neg (.add preparedControlOpened preparedControlClosed))
def preparedControlJump (limb : Nat) : Expr :=
  .mul (.mul .isTransition preparedControlTaken)
    (.add (preparedCodeBits (16*limb) true) (.neg (preparedCodeBits (649+16*limb))))
def preparedControlLabelStep : Expr :=
  .mul .isTransition (.add (.col 639 true)
    (.neg (.add preparedControlOpened (.mul preparedControlKeep (.col 639 false)))))
def preparedControlHeightStep (i : Nat) : Expr :=
  .mul .isTransition (.add (.col (640+i) true)
    (.neg (.add (.mul preparedControlOpened (.col (32+i) false))
      (.mul preparedControlKeep (.col (640+i) false)))))
def preparedControlTargetStep (limb : Nat) : Expr :=
  .mul .isTransition (.add (preparedCodeBits (649+16*limb) true)
    (.neg (.add (.mul preparedControlOpened (preparedCodeBits (607+16*limb)))
      (.mul preparedControlKeep (preparedCodeBits (649+16*limb))))))
def preparedControlSavedTarget (row : Nat → Fp) : Nat :=
  (preparedCodeLimb row 649).toNat+65536*(preparedCodeLimb row 665).toNat

theorem prepared_control_literal_boolean (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (hr : r<tr.height t)
    (i : Nat) (hi : i<682) : (tr.cell t r i).toNat≤1 := by
  have h:=localH.constr r hr _ (prepared_control_literal_condition_source.boolean i hi)
  change tr.cell t r i*(tr.cell t r i+ -(1:Fp))+ -(0:Fp)=0 at h
  apply instruction_add_boolean_bound
  grind

/-- The literal six-opcode one-hot constraint eliminates all other opcode
selectors whenever this row is a conditional branch. -/
theorem prepared_control_branch_opcode (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (hr : r<tr.height t)
    (branch : tr.cell t r 606=1) :
    (∀ i,i<4 → tr.cell t r (466+i)=0) ∧ tr.cell t r 605=0 := by
  let code : Nat → Nat:=fun i=>if i<4 then 466+i else 605+(i-4)
  have one : ∃ tag,tag<6 ∧ ∀ i,i<6 → tr.cell t r (code i)=if i=tag then 1 else 0 := by
    suffices h : ∃ tag,tag<6 ∧ ∀ i,i<6 → tr.cell t r (code (0+i))=if i=tag then 1 else 0 by
      simpa only [Nat.zero_add] using h
    apply prepared_onehot 6 0 (fun i=>tr.cell t r (code i)) (by decide)
    · intro i hi
      apply prepared_control_literal_boolean tr t r pub localH hr
      dsimp only [code]
      split <;> omega
    · have member : preparedControlLiteralExec0685∈preparedControlLiteralExecTable.constraints:=
        List.getElem_mem (l:=preparedControlLiteralExec) (n:=685) (by decide)
      have h:=localH.constr r hr _ member
      change ((tr.cell t r 466+tr.cell t r 467)+(tr.cell t r 468+tr.cell t r 469)+
        (tr.cell t r 605+tr.cell t r 606))+ -(1:Fp)=0 at h
      simp only [preparedFieldSum,code,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,ite_true,ite_false]
      grind
  obtain ⟨tag,bound,selected⟩:=one
  have five:=selected 5 (by decide)
  change tr.cell t r 606=(if 5=tag then 1 else 0) at five
  rw [branch] at five
  have eq : tag=5 := by
    by_cases eq:5=tag
    · omega
    · simp only [eq,ite_false] at five
      exact False.elim ((by decide : (1:Fp)≠0) five)
  refine ⟨?_,?_⟩
  · intro i hi
    simpa only [code,hi,ite_true,eq,show ¬i=5 by omega,ite_false] using selected i (by omega)
  · simpa only [code,Nat.reduceLT,ite_false,Nat.reduceSub,Nat.add_zero,eq,Nat.reduceEqDiff] using selected 4 (by decide)

theorem prepared_control_taken_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1) :
    preparedControlTaken.eval tr t r pub=1 := by
  change (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*(tr.cell t r 606*tr.cell t r 681)=1
  rw [active,charged,branch,nonzero];grind

/-- The two actual jump constraints bind the next numeric PC limbwise;
no single field equality is used to compare 32-bit addresses. -/
theorem prepared_control_taken_pc (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1) :
    preparedCodeExecPC (tr.cell t (r+1))=preparedControlSavedTarget (tr.cell t r) := by
  have taken:=prepared_control_taken_eval tr t r pub active charged branch nonzero
  have limb (i : Nat) (hi : i<2) : preparedCodeLimb (tr.cell t (r+1)) (16*i)=
      preparedCodeLimb (tr.cell t r) (649+16*i) := by
    have member : preparedControlJump i∈preparedControlLiteralExecTable.constraints := by
      have cases : i=0 ∨ i=1:=by omega
      rcases cases with h|h <;> subst i
      · exact List.getElem_mem (l:=preparedControlLiteralExec) (n:=732) (by decide)
      · exact List.getElem_mem (l:=preparedControlLiteralExec) (n:=733) (by decide)
    have h:=localH.constr r (by omega) _ member
    change ((if r+1=tr.height t then (0:Fp) else 1)*preparedControlTaken.eval tr t r pub)*
      ((preparedCodeBits (16*i) true).eval tr t r pub+ -(preparedCodeBits (649+16*i)).eval tr t r pub)=0 at h
    rw [if_neg (by omega),taken,prepared_code_bits_eval,prepared_code_bits_eval] at h
    simp only [Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt nonlast] at h
    grind
  unfold preparedCodeExecPC preparedControlSavedTarget
  rw [limb 0 (by decide),limb 1 (by decide)]

theorem prepared_control_taken_gates (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1) :
    preparedControlOpened.eval tr t r pub=0 ∧ preparedControlKeep.eval tr t r pub=0 := by
  have ops:=prepared_control_branch_opcode tr t r pub localH hr branch
  have opened : preparedControlOpened.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*tr.cell t r 605=0
    rw [ops.2];grind
  have taken:=prepared_control_taken_eval tr t r pub active charged branch nonzero
  refine ⟨opened,?_⟩
  change (1:Fp)+ -(preparedControlOpened.eval tr t r pub+
    (preparedControlTaken.eval tr t r pub+preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 469*tr.cell t r 639)))=0
  rw [opened,taken,ops.1 3 (by decide)];grind

private theorem control_height_at : ∀ i:Fin 9,
    preparedControlLiteralExec[774+i.val]'(by change _<870;omega)=preparedControlHeightStep i.val := by decide

/-- A successful taken branch discards the nested label and canonically
clears its saved height and target; failure and padding are not this case. -/
theorem prepared_control_taken_label (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1) :
    tr.cell t (r+1) 639=0 ∧ (∀ i,i<9 → tr.cell t (r+1) (640+i)=0) ∧
    preparedControlSavedTarget (tr.cell t (r+1))=0 := by
  have gates:=prepared_control_taken_gates tr t r pub localH (by omega) active charged branch nonzero
  have trans : (if r+1=tr.height t then (0:Fp) else 1)=1:=if_neg (by omega)
  refine ⟨?_,?_,?_⟩
  · have member : preparedControlLabelStep∈preparedControlLiteralExecTable.constraints :=
      List.getElem_mem (l:=preparedControlLiteralExec) (n:=773) (by decide)
    have h:=localH.constr r (by omega) _ member
    change (if r+1=tr.height t then (0:Fp) else 1)*(tr.cell t ((r+1)%tr.height t) 639+
      -(preparedControlOpened.eval tr t r pub+preparedControlKeep.eval tr t r pub*tr.cell t r 639))=0 at h
    rw [trans,gates.1,gates.2,Nat.mod_eq_of_lt nonlast] at h
    grind
  · intro i hi
    have member:=List.getElem_mem (l:=preparedControlLiteralExec) (n:=774+i) (by change _<870;omega)
    rw [control_height_at ⟨i,hi⟩] at member
    have h:=localH.constr r (by omega) _ member
    change (if r+1=tr.height t then (0:Fp) else 1)*(tr.cell t ((r+1)%tr.height t) (640+i)+
      -(preparedControlOpened.eval tr t r pub*tr.cell t r (32+i)+preparedControlKeep.eval tr t r pub*tr.cell t r (640+i)))=0 at h
    rw [trans,gates.1,gates.2,Nat.mod_eq_of_lt nonlast] at h
    grind
  · have limb (i : Nat) (hi : i<2) : preparedCodeLimb (tr.cell t (r+1)) (649+16*i)=0 := by
      have member : preparedControlTargetStep i∈preparedControlLiteralExecTable.constraints := by
        have cases : i=0 ∨ i=1:=by omega
        rcases cases with h|h <;> subst i
        · exact List.getElem_mem (l:=preparedControlLiteralExec) (n:=783) (by decide)
        · exact List.getElem_mem (l:=preparedControlLiteralExec) (n:=785) (by decide)
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
