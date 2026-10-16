import NearCompression.PreparedLocalsTakenStack
import NearCompression.PreparedLocalsCondition
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
theorem prepared_locals_untaken_sp (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (zero : tr.cell t r 681=0) :
    ∃ sp,0<sp ∧ sp<9 ∧ (∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) ∧
      ∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=sp-1 then 1 else 0 := by
  have hr : r<tr.height t:=by omega
  have ops:=prepared_locals_branch_opcode count tr t r pub localH hr branch
  have lz:=(prepared_locals_control_opcode_exclusive count tr t r pub localH hr 5 (by decide) branch).2
  obtain ⟨sp,bound,selected⟩:=prepared_locals_onehot count tr t r pub localH hr
  obtain ⟨nextSP,nextBound,nextSelected⟩:=prepared_locals_onehot count tr t (r+1) pub localH nonlast
  have success : preparedExecGasSuccess.eval tr t r pub=1 := by
    change ((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430)=1
    rw [active,charged];grind
  have guardMember : preparedLocalsLiteralExec1043∈(preparedLocalsLiteralExecTable count).constraints:=
    prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1043) (by decide))
  have guard:=localH.constr r hr _ guardMember
  change preparedExecGasSuccess.eval tr t r pub*(((tr.cell t r 468+tr.cell t r 606)+(tr.cell t r 684+tr.cell t r 685))*tr.cell t r 32)+ -(0:Fp)=0 at guard
  rw [success,ops.1 2 (by decide),branch,lz 1 (by decide),lz 2 (by decide)] at guard
  have emptyZero : tr.cell t r 32=0 := by grind
  have positive : 0<sp := by
    have h:=selected 0 (by decide)
    change tr.cell t r 32=(if 0=sp then 1 else 0) at h
    rw [emptyZero] at h
    by_cases eq:0=sp
    · simp only [eq,ite_true] at h
      exact False.elim ((by decide : (0:Fp)≠1) h)
    · omega
  have notTaken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [zero];grind
  have delta : preparedLocalsDelta.eval tr t r pub= -(1:Fp) := by
    change preparedExecGasSuccess.eval tr t r pub*((tr.cell t r 466+tr.cell t r 683)+ -(((tr.cell t r 467+tr.cell t r 468)+tr.cell t r 606)+tr.cell t r 684))= -(1:Fp)
    rw [success,ops.1 0 (by decide),ops.1 1 (by decide),ops.1 2 (by decide),branch,lz 0 (by decide),lz 1 (by decide)];grind
  have member : preparedLocalsSPStep∈(preparedLocalsLiteralExecTable count).constraints:=
    prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1040) (by decide))
  have h:=localH.constr r hr _ member
  change (if r+1=tr.height t then (0:Fp) else 1)*((preparedControlIndex 32 true).eval tr t r pub+
    -(preparedControlTaken.eval tr t r pub*(preparedControlIndex 640).eval tr t r pub+
      ((1:Fp)+ -preparedControlTaken.eval tr t r pub)*((preparedControlIndex 32).eval tr t r pub+preparedLocalsDelta.eval tr t r pub)))=0 at h
  rw [if_neg (by omega),notTaken,delta] at h
  have current : (preparedControlIndex 32).eval tr t r pub=Fp.ofNat sp:=
    prepared_control_index_selected (tr.cell t r) 32 sp bound selected
  have next : (preparedControlIndex 32 true).eval tr t r pub=Fp.ofNat nextSP := by
    have eq:=prepared_control_index_selected (tr.cell t (r+1)) 32 nextSP nextBound nextSelected
    simpa only [preparedControlIndex,preparedBalancedSum,Expr.eval,Expr.evalWith,rowEnv,
      instructionAddEnv,ite_true,Nat.mod_eq_of_lt nonlast,←Lean.Grind.Semiring.ofNat_eq_natCast,←Fp.ofNat_def] using eq
  rw [current,next] at h
  have fieldEq : Fp.ofNat nextSP+(1:Fp)=Fp.ofNat sp:=by grind
  have natEq:=congrArg Fp.toNat fieldEq
  change (Fp.add (Fp.ofNat nextSP) (Fp.ofNat 1)).toNat=(Fp.ofNat sp).toNat at natEq
  simp only [Fp.toNat_add,Fp.toNat_ofNat] at natEq
  change (nextSP%ZkFormal.Algebra.P+1)%ZkFormal.Algebra.P=sp%ZkFormal.Algebra.P at natEq
  rw [Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega),Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega),
    Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega)] at natEq
  have eq : nextSP=sp-1:=by omega
  exact ⟨sp,positive,bound,selected,by simpa only [eq] using nextSelected⟩

set_option maxHeartbeats 2000000 in
private theorem untaken_stack_at : ∀ slot:Fin 8,∀ limb:Fin 2,
    preparedLocalsLiteralExecBase[1113+4*slot.val+2*limb.val]'(by change _<1144;omega)=
      preparedLocalsStackStep slot.val limb.val := by decide

/-- False br_if clears exactly the condition slot; every other encoded
stack word is unchanged. The next live height is separately proved above. -/
theorem prepared_locals_untaken_stack (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (zero : tr.cell t r 681=0)
    (sp : Nat) (bound : sp<9) (selected : ∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    ∀ slot,slot<8 → preparedExecStackWord (tr.cell t (r+1)) slot=
      if slot+1=sp then 0 else preparedExecStackWord (tr.cell t r) slot := by
  have ops:=prepared_locals_branch_opcode count tr t r pub localH (by omega) branch
  have lz:=(prepared_locals_control_opcode_exclusive count tr t r pub localH (by omega) 5 (by decide) branch).2
  have success : preparedExecGasSuccess.eval tr t r pub=1 := by
    change ((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430)=1
    rw [active,charged];grind
  have notTaken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [zero];grind
  intro slot hs
  have selectedTop:=selected (slot+1) (by omega)
  have limb (i : Nat) (hi : i<2) : preparedCodeLimb (tr.cell t (r+1)) (43+32*slot+16*i)=
      if slot+1=sp then 0 else preparedCodeLimb (tr.cell t r) (43+32*slot+16*i) := by
    have member:=List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1113+4*slot+2*i) (by change _<1144;omega)
    rw [untaken_stack_at ⟨slot,hs⟩ ⟨i,hi⟩] at member
    have h:=localH.constr r (by omega) _ (prepared_locals_base_member count _ member)
    let push:=preparedExecGasSuccess.eval tr t r pub*((tr.cell t r 466+tr.cell t r 683)*tr.cell t r (32+slot))
    let write:=preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 467*((if slot+2≤8 then Expr.col (32+slot+2) false else .const 0).eval tr t r pub))
    let clear:=preparedExecGasSuccess.eval tr t r pub*((tr.cell t r 467+tr.cell t r 468+tr.cell t r 606+tr.cell t r 684)*tr.cell t r (32+slot+1))
    have pz : push=0 := by dsimp only [push];rw [ops.1 0 (by decide),lz 0 (by decide)];grind
    have wz : write=0 := by dsimp only [write];rw [ops.1 1 (by decide)];grind
    have ce : clear=tr.cell t r (32+(slot+1)) := by
      dsimp only [clear];rw [success,ops.1 1 (by decide),ops.1 2 (by decide),branch,lz 1 (by decide)]
      rw [Nat.add_assoc];grind
    change (if r+1=tr.height t then (0:Fp) else 1)*((preparedCodeBits (43+32*slot+16*i) true).eval tr t r pub+
      -(preparedControlTaken.eval tr t r pub*((preparedControlBelow slot).eval tr t r pub*
        (preparedCodeBits (43+32*slot+16*i)).eval tr t r pub)+
        ((1:Fp)+ -preparedControlTaken.eval tr t r pub)*
        (((1:Fp)+ -((push+write)+clear))*(preparedCodeBits (43+32*slot+16*i)).eval tr t r pub+
          (push*(tr.cell t r 466*(preparedCodeBits (470+16*i)).eval tr t r pub+tr.cell t r 683*(preparedLocalsRead i).eval tr t r pub)+write*(preparedCodeBits (431+16*i)).eval tr t r pub))))=0 at h
    rw [if_neg (by omega),notTaken,pz,wz,ce,selectedTop,prepared_code_bits_eval,prepared_code_bits_eval] at h
    simp only [Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt nonlast] at h
    split <;> grind
  have low:=limb 0 (by decide)
  have high:=limb 1 (by decide)
  simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero] at low high
  rw [prepared_control_stack_word,prepared_control_stack_word,low,high]
  split <;> rfl

theorem prepared_locals_untaken_stack_projection (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (zero : tr.cell t r 681=0) :
    ∃ sp,0<sp ∧ sp<9 ∧ (∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) ∧
      (∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=sp-1 then 1 else 0) ∧
      preparedExecStackWord (tr.cell t r) (sp-1)=0 ∧
      ∀ slot,slot<8 → preparedExecStackWord (tr.cell t (r+1)) slot=
        if slot+1=sp then 0 else preparedExecStackWord (tr.cell t r) slot := by
  obtain ⟨sp,positive,bound,selected,nextSelected⟩:=prepared_locals_untaken_sp count tr t r pub localH nonlast active charged branch zero
  have condition:=prepared_control_condition_sound _ tr t r pub localH (by omega)
    (prepared_locals_condition_source count) sp bound positive selected
  exact ⟨sp,positive,bound,selected,nextSelected,condition.2.mp zero,
    prepared_locals_untaken_stack count tr t r pub localH nonlast active charged branch zero sp bound selected⟩
theorem prepared_locals_untaken_pc_label (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (zero : tr.cell t r 681=0) :
    preparedCodeExecPC (tr.cell t (r+1))=preparedCodeExecPC (tr.cell t r)+1 ∧
    tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 ∧
    tr.cell t (r+1) 639=tr.cell t r 639 ∧
    (∀ i,i<9 → tr.cell t (r+1) (640+i)=tr.cell t r (640+i)) ∧
    preparedControlSavedTarget (tr.cell t (r+1))=preparedControlSavedTarget (tr.cell t r) := by
  have ops:=prepared_locals_branch_opcode count tr t r pub localH (by omega) branch
  have notTaken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [zero];grind
  have advance : preparedControlAdvance.eval tr t r pub=Fp.ofNat 1 := by
    change (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*
      ((1:Fp)+ -(tr.cell t r 469*((1:Fp)+ -tr.cell t r 639)+tr.cell t r 606*tr.cell t r 681))=1
    rw [active,charged,ops.1 3 (by decide),zero];grind
  have status:=prepared_locals_continue_status count tr t r pub localH nonlast active charged (by rw [ops.1 3 (by decide)];grind)
  have opened : preparedControlOpened.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*tr.cell t r 605=0
    rw [ops.2];grind
  have keep : preparedControlKeep.eval tr t r pub=1 := by
    change (1:Fp)+ -(preparedControlOpened.eval tr t r pub+
      (preparedControlTaken.eval tr t r pub+preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 469*tr.cell t r 639)))=1
    rw [opened,notTaken,ops.1 3 (by decide)];grind
  have labels:=prepared_locals_label_equations count tr t r pub localH nonlast
  rw [opened,keep] at labels
  refine ⟨prepared_locals_sequential_pc count tr t r pub localH nonlast notTaken 1 (by decide) advance,
    status.2.1,status.2.2,by grind,?_,?_⟩
  · intro i hi;have h:=labels.2.1 i hi;grind
  · have low:=labels.2.2 0 (by decide)
    have high:=labels.2.2 1 (by decide)
    have l : preparedCodeLimb (tr.cell t (r+1)) 649=preparedCodeLimb (tr.cell t r) 649:=by simpa only [Nat.mul_zero,Nat.add_zero] using (show _=_ from by grind)
    have h : preparedCodeLimb (tr.cell t (r+1)) 665=preparedCodeLimb (tr.cell t r) 665:=by simpa only [Nat.mul_one,Nat.reduceAdd] using (show _=_ from by grind)
    unfold preparedControlSavedTarget
    rw [l,h]

end NearCompression
