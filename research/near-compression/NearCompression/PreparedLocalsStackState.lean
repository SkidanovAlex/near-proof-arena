import NearCompression.PreparedLocalsStack
import NearCompression.PreparedLocalsDepth
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536

def preparedLocalsNextDepth (kind : PreparedLocalOp) (sp : Nat) : Nat :=
  match kind with | .get=>sp+1 | .set=>sp-1 | .tee=>sp

/-- Actual interpreter stack array, reconstructed from all physical slot
constraints. No successor stack certificate is assumed. -/
theorem prepared_locals_stack_array (kind : PreparedLocalOp) (count : Nat)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (nonlast : r+1<tr.height t) (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (old : ∀i,i<3 → tr.cell t r (466+i)=0) (branch : tr.cell t r 606=0)
    (get : tr.cell t r 683=if kind=.get then 1 else 0)
    (set : tr.cell t r 684=if kind=.set then 1 else 0)
    (tee : tr.cell t r 685=if kind=.tee then 1 else 0)
    (sp index : Nat) (bound : sp<9) (ib : index<4)
    (hot : ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0)
    (selected : ∀j,j<4 → tr.cell t r (814+j)=if j=index then 1 else 0) :
    (if kind=.get then sp<8 else 0<sp) ∧
    preparedLocalsNextDepth kind sp<9 ∧
    (∀i,i<9 → tr.cell t (r+1) (32+i)=if i=preparedLocalsNextDepth kind sp then 1 else 0) ∧
    preparedWasmStack (preparedExecGhostRow (tr.cell t (r+1))) (preparedLocalsNextDepth kind sp)=
      match kind with
      | .get=>(preparedWasmStack (preparedExecGhostRow (tr.cell t r)) sp).push
          (.i32 (UInt32.ofNat (preparedLocalsWord (tr.cell t r) index)))
      | .set=>(preparedWasmStack (preparedExecGhostRow (tr.cell t r)) sp).pop
      | .tee=>preparedWasmStack (preparedExecGhostRow (tr.cell t r)) sp := by
  obtain ⟨guard,next,nb,rel,nh⟩:=prepared_locals_depth_step kind count tr t r pub localH nonlast active charged
    old branch get set tee sp bound hot
  have nextEq : next=preparedLocalsNextDepth kind sp := by
    cases kind <;> simp only [preparedLocalsNextDepth,reduceCtorEq,ite_true,ite_false,Nat.add_zero] at rel guard ⊢ <;> omega
  have words:=prepared_locals_stack_word_next kind count tr t r pub localH nonlast active charged
    old branch get set sp index bound ib hot selected
  refine ⟨guard,by omega,nextEq ▸ nh,?_⟩
  cases kind with
  | get =>
    change (preparedWasmStack _ sp).push _=_
    have prefixEq : preparedWasmStack (preparedExecGhostRow (tr.cell t (r+1))) sp=
        preparedWasmStack (preparedExecGhostRow (tr.cell t r)) sp := by
      apply prepared_wasm_stack_congr
      intro i hi
      rw [prepared_locals_stack_word,prepared_locals_stack_word]
      have w:=words i (by omega)
      simpa only [reduceCtorEq,ite_true,ite_false,true_and,false_and,show ¬i=sp by omega] using w
    have top:=words sp (by simpa only [ite_true] using guard)
    simp only [reduceCtorEq,ite_true,ite_false,true_and,false_and] at top
    rw [prefixEq,prepared_locals_stack_word,top]
  | set =>
    obtain ⟨n,eq⟩:∃n,sp=n+1:=⟨sp-1,by simp only [reduceCtorEq,ite_false] at guard;omega⟩
    subst sp
    simp only [preparedLocalsNextDepth,Nat.add_sub_cancel,preparedWasmStack,Array.pop_push]
    apply prepared_wasm_stack_congr
    intro i hi
    rw [prepared_locals_stack_word,prepared_locals_stack_word]
    have w:=words i (by omega)
    simpa only [reduceCtorEq,ite_true,ite_false,true_and,false_and,show ¬i+1=n+1 by omega] using w
  | tee =>
    apply prepared_wasm_stack_congr
    intro i hi
    rw [prepared_locals_stack_word,prepared_locals_stack_word]
    simpa only [reduceCtorEq,ite_true,ite_false,true_and,false_and] using words i (by omega)
end NearCompression
