import NearCompression.PreparedTypedCondition
import NearCompression.PreparedTypedBranch
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem lower_guard_at : ∀count:Fin 5,∀h:Fin 9,∀j:Fin 9,j.val<h.val →
    (preparedTypedLiteralExec count)[1682+66*(4-count.val)+h.val*(h.val+1)/2+j.val]?=
      some (.add (.mul (.col (640+h.val) false) (.col (32+j.val) false)) (.neg (.const 0))) := by decide
private theorem equal_guard_at : ∀count:Fin 5,∀h:Fin 9,
    (preparedTypedLiteralExec count)[1682+66*(4-count.val)+h.val*(h.val+1)/2+h.val]?=
      some (.add (.mul preparedExecGasSuccess (.mul (.col 606 false)
        (.mul (.col (640+h.val) false) (.col (32+h.val) false)))) (.neg (.const 0))) := by decide
private theorem present_at : ∀count:Fin 5,(preparedTypedLiteralExec count)[1667+66*(4-count.val)]?=
    some (.add (.mul preparedExecGasSuccess (.mul (.col 606 false) (.add (.const 1) (.neg (.col 639 false))))) (.neg (.const 0))) := by decide

theorem prepared_typed_branch_present (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0) (branch : tr.cell t r 606=1) :
    tr.cell t r 639=1 := by
  have h:=localH.constr r hr _ (List.mem_of_getElem? (present_at ⟨count,by omega⟩))
  change (((1:Fp)+ -tr.cell t r 41)*(1+ -tr.cell t r 430))*(tr.cell t r 606*(1+ -tr.cell t r 639))+ -0=0 at h
  rw [active,charged,branch] at h
  grind
/-- The branch guard forces the saved prefix below the condition operand,
so actual extract cannot silently clamp an oversized saved height. -/
theorem prepared_typed_branch_height_lt (count : Nat) (hc : count≤4) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
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
    · have h:=localH.constr r hr _ (List.mem_of_getElem? (lower_guard_at ⟨count,by omega⟩ ⟨height,hh⟩ ⟨sp,hs⟩ less))
      change tr.cell t r (640+height)*tr.cell t r (32+sp)+ -(0:Fp)=0 at h
      rw [top,base] at h
      have impossible : (1:Fp)=0:=by grind
      exact (by decide : (1:Fp)≠0) impossible
    · have eq : sp=height:=by omega
      subst sp
      have h:=localH.constr r hr _ (List.mem_of_getElem? (equal_guard_at ⟨count,by omega⟩ ⟨height,hh⟩))
      change (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*
        (tr.cell t r 606*(tr.cell t r (640+height)*tr.cell t r (32+height)))+ -(0:Fp)=0 at h
      rw [active,charged,branch,top,base] at h
      have impossible : (1:Fp)=0:=by grind
      exact (by decide : (1:Fp)≠0) impossible


end NearCompression
