import NearCompression.PreparedLocalsBranch
import NearCompression.PreparedLocalsStack
import NearCompression.PreparedLocalsDepth
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
theorem prepared_locals_branch_height (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (branch : tr.cell t r 606=1) :
    tr.cell t r 639=1 ∧ ∃ height,height<9 ∧ ∀ i,i<9 → tr.cell t r (640+i)=if i=height then 1 else 0 := by
  have guardMember : preparedLocalsLiteralExec1046∈(preparedLocalsLiteralExecTable count).constraints:=
    prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1046) (by decide))
  have guard:=localH.constr r hr _ guardMember
  change (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*
    (tr.cell t r 606*((1:Fp)+ -tr.cell t r 639))+ -(0:Fp)=0 at guard
  rw [active,charged,branch] at guard
  have label : tr.cell t r 639=1:=by grind
  refine ⟨label,?_⟩
  apply prepared_onehot 9 640 (tr.cell t r) (by decide)
  · intro i hi
    exact prepared_locals_bits_boolean count tr t r pub localH hr _ (by omega) (by omega)
  · have member : preparedLocalsLiteralExec0818∈(preparedLocalsLiteralExecTable count).constraints:=
      prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=818) (by decide))
    have h:=localH.constr r hr _ member
    change (((tr.cell t r 640+tr.cell t r 641)+(tr.cell t r 642+tr.cell t r 643))+
      ((tr.cell t r 644+tr.cell t r 645)+(tr.cell t r 646+tr.cell t r 647))+tr.cell t r 648)+ -tr.cell t r 639=0 at h
    rw [label] at h
    simp only [preparedFieldSum,Nat.reduceAdd]
    grind

/-- The literal taken-branch SP equation selects exactly the saved height. -/
theorem prepared_locals_taken_sp (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1) :
    ∃ height,height<9 ∧ (∀ i,i<9 → tr.cell t r (640+i)=if i=height then 1 else 0) ∧
      ∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=height then 1 else 0 := by
  obtain ⟨_,height,bound,selected⟩:=prepared_locals_branch_height count tr t r pub localH (by omega) active charged branch
  obtain ⟨nextHeight,nextBound,nextSelected⟩:=prepared_locals_onehot count tr t (r+1) pub localH nonlast
  have taken:=prepared_control_taken_eval tr t r pub active charged branch nonzero
  have member : preparedLocalsSPStep∈(preparedLocalsLiteralExecTable count).constraints:=
    prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1040) (by decide))
  have h:=localH.constr r (by omega) _ member
  change (if r+1=tr.height t then (0:Fp) else 1)*((preparedControlIndex 32 true).eval tr t r pub+
    -(preparedControlTaken.eval tr t r pub*(preparedControlIndex 640).eval tr t r pub+
      ((1:Fp)+ -preparedControlTaken.eval tr t r pub)*((preparedControlIndex 32).eval tr t r pub+preparedLocalsDelta.eval tr t r pub)))=0 at h
  rw [if_neg (by omega),taken] at h
  have current : (preparedControlIndex 640).eval tr t r pub=Fp.ofNat height :=
    prepared_control_index_selected (tr.cell t r) 640 height bound selected
  have next : (preparedControlIndex 32 true).eval tr t r pub=Fp.ofNat nextHeight := by
    have eq:=prepared_control_index_selected (tr.cell t (r+1)) 32 nextHeight nextBound nextSelected
    simpa only [preparedControlIndex,preparedBalancedSum,Expr.eval,Expr.evalWith,rowEnv,
      instructionAddEnv,ite_true,Nat.mod_eq_of_lt nonlast,←Lean.Grind.Semiring.ofNat_eq_natCast,←Fp.ofNat_def] using eq
  rw [current,next] at h
  have fieldEq : Fp.ofNat nextHeight=Fp.ofNat height:=by grind
  have natEq:=congrArg Fp.toNat fieldEq
  simp only [Fp.toNat_ofNat] at natEq
  rw [Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega),Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega)] at natEq
  exact ⟨height,bound,selected,by simpa only [natEq] using nextSelected⟩

set_option maxHeartbeats 2000000 in
private theorem control_stack_at : ∀ slot:Fin 8,∀ limb:Fin 2,
    preparedLocalsLiteralExecBase[1113+4*slot.val+2*limb.val]'(by change _<1144;omega)=
      preparedLocalsStackStep slot.val limb.val := by decide

/-- Taken-branch stack writes preserve precisely the saved prefix and clear
every slot at or above the saved height. Both limbs are constrained. -/
theorem prepared_locals_taken_stack (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1)
    (height : Nat) (bound : height<9)
    (selected : ∀ i,i<9 → tr.cell t r (640+i)=if i=height then 1 else 0) :
    ∀ slot,slot<8 → preparedExecStackWord (tr.cell t (r+1)) slot=
      if slot<height then preparedExecStackWord (tr.cell t r) slot else 0 := by
  have taken:=prepared_control_taken_eval tr t r pub active charged branch nonzero
  intro slot hs
  have below:=prepared_control_below_selected tr t r pub slot height hs bound selected
  have limb (i : Nat) (hi : i<2) : preparedCodeLimb (tr.cell t (r+1)) (43+32*slot+16*i)=
      if slot<height then preparedCodeLimb (tr.cell t r) (43+32*slot+16*i) else 0 := by
    have member:=List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1113+4*slot+2*i) (by change _<1144;omega)
    rw [control_stack_at ⟨slot,hs⟩ ⟨i,hi⟩] at member
    have h:=localH.constr r (by omega) _ (prepared_locals_base_member count _ member)
    change (if r+1=tr.height t then (0:Fp) else 1)*((preparedCodeBits (43+32*slot+16*i) true).eval tr t r pub+
      -(preparedControlTaken.eval tr t r pub*((preparedControlBelow slot).eval tr t r pub*
          (preparedCodeBits (43+32*slot+16*i)).eval tr t r pub)+
        ((1:Fp)+ -preparedControlTaken.eval tr t r pub)*_))=0 at h
    rw [if_neg (by omega),taken,below,prepared_code_bits_eval,prepared_code_bits_eval] at h
    simp only [Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt nonlast] at h
    split <;> grind
  have low:=limb 0 (by decide)
  have high:=limb 1 (by decide)
  simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero] at low high
  rw [prepared_control_stack_word,prepared_control_stack_word,low,high]
  split <;> rfl

/-- Combined taken-branch projection derives the saved height internally.
The next live stack is exactly the saved prefix, with canonical zero padding. -/
theorem prepared_locals_taken_stack_projection (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1) :
    ∃ height,height<9 ∧ (∀ i,i<9 → tr.cell t r (640+i)=if i=height then 1 else 0) ∧
      (∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=height then 1 else 0) ∧
      ∀ slot,slot<8 → preparedExecStackWord (tr.cell t (r+1)) slot=
        if slot<height then preparedExecStackWord (tr.cell t r) slot else 0 := by
  obtain ⟨height,bound,selected,nextSelected⟩:=prepared_locals_taken_sp count tr t r pub localH nonlast active charged branch nonzero
  exact ⟨height,bound,selected,nextSelected,prepared_locals_taken_stack count tr t r pub localH nonlast
    active charged branch nonzero height bound selected⟩

end NearCompression
