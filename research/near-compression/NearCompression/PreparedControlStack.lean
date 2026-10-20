import NearCompression.PreparedControlBranch

set_option maxRecDepth 65536
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm

def preparedControlIndex (base : Nat) (next : Bool := false) : Expr :=
  .add (preparedBalancedSum (fun i=>.mul (.const i) (.col (base+i) next)) 3 0)
    (.mul (.const 8) (.col (base+8) next))
def preparedControlDelta : Expr :=
  .mul preparedExecGasSuccess (.add (.col 466 false)
    (.neg (.add (.add (.col 467 false) (.col 468 false)) (.col 606 false))))
def preparedControlSPStep : Expr :=
  .mul .isTransition (.add (preparedControlIndex 32 true)
    (.neg (.add (.mul preparedControlTaken (preparedControlIndex 640))
      (.mul (.add (.const 1) (.neg preparedControlTaken))
        (.add (preparedControlIndex 32) preparedControlDelta)))))

theorem prepared_control_index_selected (row : Nat → Fp) (base height : Nat) (bound : height<9)
    (selected : ∀ i,i<9 → row (base+i)=if i=height then 1 else 0) :
    (preparedControlIndex base).evalWith (instructionAddEnv row)=Fp.ofNat height := by
  have h0:=selected 0 (by decide)
  have h1:=selected 1 (by decide)
  have h2:=selected 2 (by decide)
  have h3:=selected 3 (by decide)
  have h4:=selected 4 (by decide)
  have h5:=selected 5 (by decide)
  have h6:=selected 6 (by decide)
  have h7:=selected 7 (by decide)
  have h8:=selected 8 (by decide)
  have cases : height=0 ∨ height=1 ∨ height=2 ∨ height=3 ∨ height=4 ∨ height=5 ∨ height=6 ∨ height=7 ∨ height=8:=by omega
  simp only [preparedControlIndex,preparedBalancedSum,Expr.evalWith,instructionAddEnv,Nat.reduceAdd,Nat.reducePow]
  rw [h0,h1,h2,h3,h4,h5,h6,h7,h8]
  rcases cases with h|h|h|h|h|h|h|h|h <;> subst height
  all_goals simp only [Nat.reduceEqDiff,ite_true,ite_false,←Fp.ofNat_def]
  all_goals grind

/-- The successful branch guard requires an active nested label; its saved
height is a one-hot bounded value, not an unconstrained field integer. -/
theorem prepared_control_branch_height (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (branch : tr.cell t r 606=1) :
    tr.cell t r 639=1 ∧ ∃ height,height<9 ∧ ∀ i,i<9 → tr.cell t r (640+i)=if i=height then 1 else 0 := by
  have guardMember : preparedControlLiteralExec0772∈preparedControlLiteralExecTable.constraints:=
    List.getElem_mem (l:=preparedControlLiteralExec) (n:=772) (by decide)
  have guard:=localH.constr r hr _ guardMember
  change (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*
    (tr.cell t r 606*((1:Fp)+ -tr.cell t r 639))+ -(0:Fp)=0 at guard
  rw [active,charged,branch] at guard
  have label : tr.cell t r 639=1:=by grind
  refine ⟨label,?_⟩
  apply prepared_onehot 9 640 (tr.cell t r) (by decide)
  · intro i hi
    exact prepared_control_literal_boolean tr t r pub localH hr _ (by omega)
  · have member : preparedControlLiteralExec0683∈preparedControlLiteralExecTable.constraints:=
      List.getElem_mem (l:=preparedControlLiteralExec) (n:=683) (by decide)
    have h:=localH.constr r hr _ member
    change (((tr.cell t r 640+tr.cell t r 641)+(tr.cell t r 642+tr.cell t r 643))+
      ((tr.cell t r 644+tr.cell t r 645)+(tr.cell t r 646+tr.cell t r 647))+tr.cell t r 648)+ -tr.cell t r 639=0 at h
    rw [label] at h
    simp only [preparedFieldSum,Nat.reduceAdd]
    grind

/-- The literal taken-branch SP equation selects exactly the saved height. -/
theorem prepared_control_taken_sp (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1) :
    ∃ height,height<9 ∧ (∀ i,i<9 → tr.cell t r (640+i)=if i=height then 1 else 0) ∧
      ∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=height then 1 else 0 := by
  obtain ⟨_,height,bound,selected⟩:=prepared_control_branch_height tr t r pub localH (by omega) active charged branch
  obtain ⟨nextHeight,nextBound,nextSelected⟩:=prepared_control_literal_onehot tr t (r+1) pub localH nonlast
  have taken:=prepared_control_taken_eval tr t r pub active charged branch nonzero
  have member : preparedControlSPStep∈preparedControlLiteralExecTable.constraints:=
    List.getElem_mem (l:=preparedControlLiteralExec) (n:=766) (by decide)
  have h:=localH.constr r (by omega) _ member
  change (if r+1=tr.height t then (0:Fp) else 1)*((preparedControlIndex 32 true).eval tr t r pub+
    -(preparedControlTaken.eval tr t r pub*(preparedControlIndex 640).eval tr t r pub+
      ((1:Fp)+ -preparedControlTaken.eval tr t r pub)*((preparedControlIndex 32).eval tr t r pub+preparedControlDelta.eval tr t r pub)))=0 at h
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

def preparedControlBelow (slot : Nat) : Expr :=
  let term:=fun i=>Expr.col (640+(slot+1)+i) false
  match slot with
  | 0=>preparedBalancedSum term 3 0
  | 1=>.add (preparedBalancedSum term 2 0) (.add (.add (term 4) (term 5)) (term 6))
  | 2=>.add (preparedBalancedSum term 2 0) (.add (term 4) (term 5))
  | 3=>.add (preparedBalancedSum term 2 0) (term 4)
  | 4=>preparedBalancedSum term 2 0
  | 5=>.add (.add (term 0) (term 1)) (term 2)
  | 6=>.add (term 0) (term 1)
  | 7=>term 0
  | _=>.const 0

def preparedControlStackStep (slot limb : Nat) : Expr :=
  let old:=preparedCodeBits (43+32*slot+16*limb)
  let push:=Expr.mul preparedExecGasSuccess (.mul (.col 466 false) (.col (32+slot) false))
  let write:=Expr.mul preparedExecGasSuccess (.mul (.col 467 false)
    (if slot+2≤8 then .col (32+slot+2) false else .const 0))
  let clear:=Expr.mul preparedExecGasSuccess (.mul (.add (.add (.col 467 false) (.col 468 false)) (.col 606 false))
    (.col (32+slot+1) false))
  let linear:=Expr.add (.mul (.add (.const 1) (.neg (.add (.add push write) clear))) old)
    (.add (.mul push (preparedCodeBits (470+16*limb))) (.mul write (preparedCodeBits (431+16*limb))))
  .mul .isTransition (.add (preparedCodeBits (43+32*slot+16*limb) true)
    (.neg (.add (.mul preparedControlTaken (.mul (preparedControlBelow slot) old))
      (.mul (.add (.const 1) (.neg preparedControlTaken)) linear))))

theorem prepared_control_below_selected (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (slot height : Nat) (hs : slot<8) (hh : height<9)
    (selected : ∀ i,i<9 → tr.cell t r (640+i)=if i=height then 1 else 0) :
    (preparedControlBelow slot).eval tr t r pub=if slot<height then 1 else 0 := by
  have h0:=selected 0 (by decide)
  have h1:=selected 1 (by decide)
  have h2:=selected 2 (by decide)
  have h3:=selected 3 (by decide)
  have h4:=selected 4 (by decide)
  have h5:=selected 5 (by decide)
  have h6:=selected 6 (by decide)
  have h7:=selected 7 (by decide)
  have h8:=selected 8 (by decide)
  have slots : slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=3 ∨ slot=4 ∨ slot=5 ∨ slot=6 ∨ slot=7:=by omega
  have heights : height=0 ∨ height=1 ∨ height=2 ∨ height=3 ∨ height=4 ∨ height=5 ∨ height=6 ∨ height=7 ∨ height=8:=by omega
  rcases slots with h|h|h|h|h|h|h|h <;> subst slot
  all_goals simp only [preparedControlBelow,preparedBalancedSum,Expr.eval,Expr.evalWith,rowEnv,
    Nat.reduceAdd,Nat.reducePow,Bool.false_eq_true,ite_false]
  all_goals simp only [Nat.reduceAdd] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  all_goals simp only [h0,h1,h2,h3,h4,h5,h6,h7,h8]
  all_goals rcases heights with h|h|h|h|h|h|h|h|h <;> subst height
  all_goals simp only [Nat.reduceEqDiff,Nat.reduceLT,ite_true,ite_false]
  all_goals grind

set_option maxHeartbeats 2000000 in
private theorem control_stack_at : ∀ slot:Fin 8,∀ limb:Fin 2,
    preparedControlLiteralExec[839+4*slot.val+2*limb.val]'(by change _<870;omega)=
      preparedControlStackStep slot.val limb.val := by decide

/-- Taken-branch stack writes preserve precisely the saved prefix and clear
every slot at or above the saved height. Both limbs are constrained. -/
theorem prepared_control_taken_stack (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
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
    have member:=List.getElem_mem (l:=preparedControlLiteralExec) (n:=839+4*slot+2*i) (by change _<870;omega)
    rw [control_stack_at ⟨slot,hs⟩ ⟨i,hi⟩] at member
    have h:=localH.constr r (by omega) _ member
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
theorem prepared_control_taken_stack_projection (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1) :
    ∃ height,height<9 ∧ (∀ i,i<9 → tr.cell t r (640+i)=if i=height then 1 else 0) ∧
      (∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=height then 1 else 0) ∧
      ∀ slot,slot<8 → preparedExecStackWord (tr.cell t (r+1)) slot=
        if slot<height then preparedExecStackWord (tr.cell t r) slot else 0 := by
  obtain ⟨height,bound,selected,nextSelected⟩:=prepared_control_taken_sp tr t r pub localH nonlast active charged branch nonzero
  exact ⟨height,bound,selected,nextSelected,prepared_control_taken_stack tr t r pub localH nonlast
    active charged branch nonzero height bound selected⟩

end NearCompression
