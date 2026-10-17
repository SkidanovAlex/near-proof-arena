import NearCompression.PreparedLocalsSequential
import NearCompression.PreparedControlBranchBounds
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
private theorem guard_index : ∀ h:Fin 9,∀ j:Fin 9,1061+h.val*(h.val+1)/2+j.val<1144 := by decide

set_option maxHeartbeats 2000000 in
private theorem lower_guard_at : ∀ h:Fin 9,∀ j:Fin 9,j.val<h.val →
    preparedLocalsLiteralExecBase[1061+h.val*(h.val+1)/2+j.val]'(by change _<1144; exact guard_index h j)=
      .add (.mul (.col (640+h.val) false) (.col (32+j.val) false)) (.neg (.const 0)) := by decide
set_option maxHeartbeats 2000000 in
private theorem equal_guard_at : ∀ h:Fin 9,
    preparedLocalsLiteralExecBase[1061+h.val*(h.val+1)/2+h.val]'(by change _<1144; exact guard_index h h)=
      .add (.mul preparedExecGasSuccess (.mul (.col 606 false)
        (.mul (.col (640+h.val) false) (.col (32+h.val) false)))) (.neg (.const 0)) := by decide

/-- The branch guard forces the saved prefix below the condition operand,
so actual extract cannot silently clamp an oversized saved height. -/
theorem prepared_locals_branch_height_lt (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (branch : tr.cell t r 606=1)
    (sp height : Nat) (hs : sp<9) (hh : height<9)
    (selected : ∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (saved : ∀ i,i<9 → tr.cell t r (640+i)=if i=height then 1 else 0) : height<sp := by
  have top : tr.cell t r (32+sp)=1:=by simpa only [ite_true] using selected sp hs
  have base : tr.cell t r (640+height)=1:=by simpa only [ite_true] using saved height hh
  by_cases lt:height<sp
  · exact lt
  · exfalso
    by_cases less:sp<height
    · have index : 1061+height*(height+1)/2+sp<1144 := guard_index ⟨height,hh⟩ ⟨sp,hs⟩
      have member:=List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1061+height*(height+1)/2+sp) index
      have identity:=lower_guard_at ⟨height,hh⟩ ⟨sp,hs⟩ less
      dsimp only at identity
      have member' := Eq.mp (congrArg (fun e => e∈preparedLocalsLiteralExecBase) identity) member
      have h:=localH.constr r hr _ (prepared_locals_base_member count _ member')
      change tr.cell t r (640+height)*tr.cell t r (32+sp)+ -(0:Fp)=0 at h
      rw [top,base] at h
      have impossible : (1:Fp)=0:=by grind
      exact (by decide : (1:Fp)≠0) impossible
    · have eq : sp=height:=by omega
      subst sp
      have index : 1061+height*(height+1)/2+height<1144 := guard_index ⟨height,hh⟩ ⟨height,hh⟩
      have member:=List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1061+height*(height+1)/2+height) index
      have identity:=equal_guard_at ⟨height,hh⟩
      dsimp only at identity
      have member' := Eq.mp (congrArg (fun e => e∈preparedLocalsLiteralExecBase) identity) member
      have h:=localH.constr r hr _ (prepared_locals_base_member count _ member')
      change (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*
        (tr.cell t r 606*(tr.cell t r (640+height)*tr.cell t r (32+height)))+ -(0:Fp)=0 at h
      rw [active,charged,branch,top,base] at h
      have impossible : (1:Fp)=0:=by grind
      exact (by decide : (1:Fp)≠0) impossible

theorem prepared_locals_stack_word_bound (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (slot : Nat) (bound : slot<8) : preparedExecStackWord (tr.cell t r) slot<2^32 := by
  have low:=prepared_locals_literal_limb count tr t r pub localH hr (43+32*slot) (by omega)
  have high:=prepared_locals_literal_limb count tr t r pub localH hr (43+32*slot+16) (by omega)
  rw [prepared_control_stack_word]
  omega


end NearCompression
