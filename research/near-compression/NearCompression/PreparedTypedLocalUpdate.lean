import NearCompression.PreparedTypedLocalIndex
import NearCompression.PreparedTypedLocalPreserve
import NearCompression.PreparedTypedEqzGuard
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem update_at : ∀count:Fin 5,∀slot:Fin 4,∀limb:Fin 4,
    (preparedTypedLiteralExec count)[1565+66*(4-count.val)+4*slot.val+limb.val]?=some (preparedTypedLocalStep slot limb) := by decide

theorem prepared_typed_local_limb_step (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (write : tr.cell t r 684+tr.cell t r 685=1)
    (sp index : Nat) (sb : sp<9) (positive : 0<sp) (ib : index<4)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (selected : ∀i,i<4 → tr.cell t r (814+i)=if i=index then 1 else 0)
    (slot limb : Nat) (hs : slot<4) (hl : limb<4) :
    preparedTypedLocalLimb (tr.cell t (r+1)) slot limb=
      if slot=index then preparedTypedStackLimb (tr.cell t r) (sp-1) limb else preparedTypedLocalLimb (tr.cell t r) slot limb := by
  have h:=localH.constr r (by omega) _ (List.mem_of_getElem? (update_at ⟨count,by omega⟩ ⟨slot,hs⟩ ⟨limb,hl⟩))
  let w:=(preparedExecGasSuccess.eval tr t r pub)*((tr.cell t r 684+tr.cell t r 685)*tr.cell t r (814+slot))
  have we:w=if slot=index then 1 else 0 := by
    change (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*_= _
    rw [active,charged,write,selected slot hs];split <;> grind
  change (if r+1=tr.height t then (0:Fp) else 1)*
    ((preparedCodeBits (preparedTypedLocalBase slot limb) true).eval tr t r pub+
      -(((1:Fp)+ -w)*(preparedCodeBits (preparedTypedLocalBase slot limb)).eval tr t r pub+
        w*(preparedTypedSelectedLimb limb).eval tr t r pub))=0 at h
  rw [if_neg (by omega),we,prepared_code_bits_eval,prepared_code_bits_eval,
    prepared_typed_selected_limb tr t r pub sp limb sb positive hot] at h
  simp only [ite_true,Bool.false_eq_true,ite_false,Nat.mod_eq_of_lt nonlast] at h
  unfold preparedTypedLocalLimb
  split <;> rename_i z <;> simp only [z,ite_true,ite_false] at h <;> grind

def preparedTypedSelectedLocalType : Expr :=
  preparedBalancedSum (fun i=>.mul (.col (814+i) false) (.col (1210+i) false)) 2 0
def preparedTypedStoreTypeGuard : Expr :=
  .mul (.mul preparedExecGasSuccess (.add (.col 684 false) (.col 685 false)))
    (.add preparedTypedSelectedType (.neg preparedTypedSelectedLocalType))
private theorem type_at : ∀count:Fin 5,
    (preparedTypedLiteralExec count)[1558+66*(4-count.val)]?=some preparedTypedStoreTypeGuard := by decide

theorem prepared_typed_selected_type_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (sp : Nat) (sb : sp<9) (positive : 0<sp)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    preparedTypedSelectedType.eval tr t r pub=tr.cell t r (1074+(sp-1)) := by
  change ((tr.cell t r 33*tr.cell t r 1074+tr.cell t r 34*tr.cell t r 1075)+
    (tr.cell t r 35*tr.cell t r 1076+tr.cell t r 36*tr.cell t r 1077))+
    ((tr.cell t r 37*tr.cell t r 1078+tr.cell t r 38*tr.cell t r 1079)+
    (tr.cell t r 39*tr.cell t r 1080+tr.cell t r 40*tr.cell t r 1081))=_
  have h1:=hot 1 (by decide);have h2:=hot 2 (by decide)
  have h3:=hot 3 (by decide);have h4:=hot 4 (by decide)
  have h5:=hot 5 (by decide);have h6:=hot 6 (by decide)
  have h7:=hot 7 (by decide);have h8:=hot 8 (by decide)
  rw [h1,h2,h3,h4,h5,h6,h7,h8]
  have cases : sp=1 ∨ sp=2 ∨ sp=3 ∨ sp=4 ∨ sp=5 ∨ sp=6 ∨ sp=7 ∨ sp=8:=by omega
  rcases cases with z|z|z|z|z|z|z|z <;> subst sp
  all_goals simp only [Nat.reduceEqDiff,ite_true,ite_false]
  all_goals grind

theorem prepared_typed_store_type (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (write : tr.cell t r 684+tr.cell t r 685=1)
    (sp index : Nat) (sb : sp<9) (positive : 0<sp) (ib : index<4)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (selected : ∀i,i<4 → tr.cell t r (814+i)=if i=index then 1 else 0) :
    tr.cell t r (1074+(sp-1))=tr.cell t r (1210+index) := by
  have h:=localH.constr r hr _ (List.mem_of_getElem? (type_at ⟨count,by omega⟩))
  change (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430)*(tr.cell t r 684+tr.cell t r 685))*
    (preparedTypedSelectedType.eval tr t r pub+ -preparedTypedSelectedLocalType.eval tr t r pub)=0 at h
  have loc:preparedTypedSelectedLocalType.eval tr t r pub=tr.cell t r (1210+index) := by
    change (tr.cell t r 814*tr.cell t r 1210+tr.cell t r 815*tr.cell t r 1211)+
      (tr.cell t r 816*tr.cell t r 1212+tr.cell t r 817*tr.cell t r 1213)=_
    have a:=selected 0 (by decide);have b:=selected 1 (by decide)
    have c:=selected 2 (by decide);have d:=selected 3 (by decide)
    rw [a,b,c,d]
    have cases:index=0 ∨ index=1 ∨ index=2 ∨ index=3:=by omega
    rcases cases with z|z|z|z <;> subst index
    all_goals simp only [Nat.reduceEqDiff,ite_true,ite_false]
    all_goals grind
  rw [active,charged,write,prepared_typed_selected_type_eval tr t r pub sp sb positive hot,loc] at h
  grind

theorem prepared_typed_local_store_value (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (write : tr.cell t r 684+tr.cell t r 685=1)
    (sp index : Nat) (sb : sp<9) (positive : 0<sp) (ib : index<4)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (selected : ∀i,i<4 → tr.cell t r (814+i)=if i=index then 1 else 0)
    (slot : Nat) (hs : slot<4) :
    preparedTypedLocalValue (tr.cell t (r+1)) slot=
      if slot=index then preparedTypedStackValue (tr.cell t r) (sp-1) else preparedTypedLocalValue (tr.cell t r) slot := by
  have limbs:=prepared_typed_local_limb_step count hc tr t r pub localH nonlast active charged write sp index sb positive ib hot selected slot
  have a:=limbs 0 hs (by decide);have b:=limbs 1 hs (by decide)
  have c:=limbs 2 hs (by decide);have d:=limbs 3 hs (by decide)
  have tag:tr.cell t (r+1) (1210+slot)=tr.cell t r (1210+slot):=
    (prepared_typed_source_local_type count hc tr t (r+1) pub localH nonlast slot hs).trans
      (prepared_typed_source_local_type count hc tr t r pub localH (by omega) slot hs).symm
  by_cases z:slot=index
  · subst slot
    simp only [ite_true] at a b c d ⊢
    have ty:=prepared_typed_store_type count hc tr t r pub localH (by omega) active charged write sp index sb positive ib hot selected
    have word:preparedTypedLocalWord (tr.cell t (r+1)) index=preparedTypedStackWord (tr.cell t r) (sp-1) := by
      unfold preparedTypedLocalWord preparedTypedStackWord instructionAdd64Word
      rw [a,b,c,d]
    simp only [preparedTypedLocalValue,preparedTypedStackValue,tag,←ty,word]
  · simp only [z,ite_false] at a b c d ⊢
    have word:preparedTypedLocalWord (tr.cell t (r+1)) slot=preparedTypedLocalWord (tr.cell t r) slot := by
      unfold preparedTypedLocalWord instructionAdd64Word
      rw [a,b,c,d]
    simp only [preparedTypedLocalValue,tag,word]
end NearCompression
