import NearCompression.PreparedLocalsFrameWrite
import NearCompression.PreparedControlStack
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536

def preparedLocalsRead (limb : Nat) : Expr :=
  preparedBalancedSum (fun j=>.mul (.col (814+j) false) (preparedCodeBits (686+32*j+16*limb))) 2 0

def preparedLocalsStackStep (slot limb : Nat) : Expr :=
  let old:=preparedCodeBits (43+32*slot+16*limb)
  let push:=Expr.mul preparedExecGasSuccess (.mul (.add (.col 466 false) (.col 683 false)) (.col (32+slot) false))
  let pushed:=Expr.add (.mul (.col 466 false) (preparedCodeBits (470+16*limb)))
    (.mul (.col 683 false) (preparedLocalsRead limb))
  let write:=Expr.mul preparedExecGasSuccess (.mul (.col 467 false)
    (if slot+2≤8 then .col (32+slot+2) false else .const 0))
  let clear:=Expr.mul preparedExecGasSuccess (.mul (.add (.add (.add (.col 467 false) (.col 468 false)) (.col 606 false)) (.col 684 false))
    (.col (32+slot+1) false))
  let linear:=Expr.add (.mul (.add (.const 1) (.neg (.add (.add push write) clear))) old)
    (.add (.mul push pushed) (.mul write (preparedCodeBits (431+16*limb))))
  .mul .isTransition (.add (preparedCodeBits (43+32*slot+16*limb) true)
    (.neg (.add (.mul preparedControlTaken (.mul (preparedControlBelow slot) old))
      (.mul (.add (.const 1) (.neg preparedControlTaken)) linear))))

set_option maxHeartbeats 2000000 in
private theorem locals_stack_at : ∀ slot:Fin 8,∀ limb:Fin 2,
    preparedLocalsLiteralExecBase[1113+4*slot.val+2*limb.val]'(by change _<1144;omega)=
      preparedLocalsStackStep slot.val limb.val := by decide

theorem prepared_locals_read_selected (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (index limb : Nat) (bound : index<4)
    (selected : ∀j,j<4 → tr.cell t r (814+j)=if j=index then 1 else 0) :
    (preparedLocalsRead limb).eval tr t r pub=preparedCodeLimb (tr.cell t r) (686+32*index+16*limb) := by
  have h0:=selected 0 (by decide)
  have h1:=selected 1 (by decide)
  have h2:=selected 2 (by decide)
  have h3:=selected 3 (by decide)
  change tr.cell t r 814*(preparedCodeBits (686+32*0+16*limb)).eval tr t r pub+
      tr.cell t r 815*(preparedCodeBits (686+32*1+16*limb)).eval tr t r pub+
      (tr.cell t r 816*(preparedCodeBits (686+32*2+16*limb)).eval tr t r pub+
      tr.cell t r 817*(preparedCodeBits (686+32*3+16*limb)).eval tr t r pub)=_
  rw [h0,h1,h2,h3]
  have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3:=by omega
  rcases cases with eq|eq|eq|eq <;> subst index
  all_goals simp only [Nat.reduceEqDiff,ite_true,ite_false,prepared_code_bits_eval,Bool.false_eq_true]
  all_goals grind

/-- Both physical limbs of every stack slot obey get push/set pop/tee keep.
Canonical zero padding is retained by the pop clearing equation. -/
theorem prepared_locals_stack_limb (kind : PreparedLocalOp) (count : Nat)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (nonlast : r+1<tr.height t) (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (old : ∀i,i<3 → tr.cell t r (466+i)=0) (branch : tr.cell t r 606=0)
    (get : tr.cell t r 683=if kind=.get then 1 else 0)
    (set : tr.cell t r 684=if kind=.set then 1 else 0)
    (sp index : Nat) (bound : sp<9) (ib : index<4)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (selected : ∀j,j<4 → tr.cell t r (814+j)=if j=index then 1 else 0)
    (slot limb : Nat) (hs : slot<8) (hl : limb<2) :
    preparedCodeLimb (tr.cell t (r+1)) (43+32*slot+16*limb)=
      if kind=.get ∧ slot=sp then preparedCodeLimb (tr.cell t r) (686+32*index+16*limb)
      else if kind=.set ∧ slot+1=sp then 0 else preparedCodeLimb (tr.cell t r) (43+32*slot+16*limb) := by
  have member:=List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1113+4*slot+2*limb) (by change _<1144;omega)
  rw [locals_stack_at ⟨slot,hs⟩ ⟨limb,hl⟩] at member
  have h:=localH.constr r (by omega) _ (prepared_locals_base_member count _ member)
  have success : preparedExecGasSuccess.eval tr t r pub=1 := by
    change ((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430)=1
    rw [active,charged];grind
  have noTaken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [branch];grind
  have read:=prepared_locals_read_selected tr t r pub index limb ib selected
  change (if r+1=tr.height t then (0:Fp) else 1)*
    ((preparedCodeBits (43+32*slot+16*limb) true).eval tr t r pub+
    -(preparedControlTaken.eval tr t r pub*((preparedControlBelow slot).eval tr t r pub*(preparedCodeBits (43+32*slot+16*limb)).eval tr t r pub)+
    ((1:Fp)+ -preparedControlTaken.eval tr t r pub)*_))=0 at h
  rw [ite_eq_right (by omega),noTaken] at h
  have conditional : (if slot+2≤8 then Expr.col (32+slot+2) false else .const 0).eval tr t r pub=
      (if slot+2≤8 then tr.cell t r (32+slot+2) else 0) := by split <;> rfl
  -- Expose only the linear stack expression, preserving the bit decoders.
  change 1*((preparedCodeBits (43+32*slot+16*limb) true).eval tr t r pub+
    -(0*((preparedControlBelow slot).eval tr t r pub*(preparedCodeBits (43+32*slot+16*limb)).eval tr t r pub)+
    (1+ -0)*((1+ -((preparedExecGasSuccess.eval tr t r pub*((tr.cell t r 466+tr.cell t r 683)*tr.cell t r (32+slot))+
      preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 467*((if slot+2≤8 then Expr.col (32+slot+2) false else .const 0).eval tr t r pub)))+
      preparedExecGasSuccess.eval tr t r pub*((tr.cell t r 467+tr.cell t r 468+tr.cell t r 606+tr.cell t r 684)*tr.cell t r (32+slot+1))))*
        (preparedCodeBits (43+32*slot+16*limb)).eval tr t r pub+
      (preparedExecGasSuccess.eval tr t r pub*((tr.cell t r 466+tr.cell t r 683)*tr.cell t r (32+slot))*
        (tr.cell t r 466*(preparedCodeBits (470+16*limb)).eval tr t r pub+tr.cell t r 683*(preparedLocalsRead limb).eval tr t r pub)+
      preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 467*((if slot+2≤8 then Expr.col (32+slot+2) false else .const 0).eval tr t r pub))*
        (preparedCodeBits (431+16*limb)).eval tr t r pub))))=0 at h
  rw [conditional,success,old 0 (by decide),old 1 (by decide),old 2 (by decide),branch,get,set,read,
    hot slot (by omega)] at h
  have top:=hot (slot+1) (by omega)
  have base : 32+(slot+1)=32+slot+1 := by omega
  rw [base] at top
  rw [top,prepared_code_bits_eval,prepared_code_bits_eval] at h
  simp only [Bool.false_eq_true,ite_true,ite_false,Nat.mod_eq_of_lt nonlast] at h
  cases kind <;> simp only [reduceCtorEq,ite_true,ite_false,true_and,false_and] at h ⊢
  all_goals grind
theorem prepared_locals_stack_word_next (kind : PreparedLocalOp) (count : Nat)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (nonlast : r+1<tr.height t) (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (old : ∀i,i<3 → tr.cell t r (466+i)=0) (branch : tr.cell t r 606=0)
    (get : tr.cell t r 683=if kind=.get then 1 else 0)
    (set : tr.cell t r 684=if kind=.set then 1 else 0)
    (sp index : Nat) (bound : sp<9) (ib : index<4)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (selected : ∀j,j<4 → tr.cell t r (814+j)=if j=index then 1 else 0)
    (slot : Nat) (hs : slot<8) :
    preparedLocalsStackWord (tr.cell t (r+1)) slot=
      if kind=.get ∧ slot=sp then preparedLocalsWord (tr.cell t r) index
      else if kind=.set ∧ slot+1=sp then 0 else preparedLocalsStackWord (tr.cell t r) slot := by
  have low:=prepared_locals_stack_limb kind count tr t r pub localH nonlast active charged old branch get set
    sp index bound ib hot selected slot 0 hs (by decide)
  have high:=prepared_locals_stack_limb kind count tr t r pub localH nonlast active charged old branch get set
    sp index bound ib hot selected slot 1 hs (by decide)
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at low high
  have hs : 43+32*slot+16=59+32*slot := by omega
  have hi : 686+32*index+16=702+32*index := by omega
  rw [hs,hi] at high
  unfold preparedLocalsStackWord preparedLocalsWord
  rw [low,high]
  split
  · rfl
  · split <;> rfl

end NearCompression
