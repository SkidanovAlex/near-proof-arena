import NearCompression.PreparedControlStack
import NearCompression.PreparedControlBlock
set_option maxRecDepth 65536
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm

set_option maxHeartbeats 2000000 in
private theorem frame_stack_at : ∀ slot:Fin 8,∀ limb:Fin 2,
    preparedControlLiteralExec[839+4*slot.val+2*limb.val]'(by change _<870;omega)=
      preparedControlStackStep slot.val limb.val := by decide

/-- Block and end leave every stack slot unchanged; this follows from the
actual full stack-write constraints, including their taken-branch factors. -/
theorem prepared_control_frame_stack (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (tag : Nat) (mode : tag=3 ∨ tag=4)
    (chosen : tr.cell t r (preparedControlOpcodeColumn tag)=1) :
    ∀ slot,slot<8 → preparedExecStackWord (tr.cell t (r+1)) slot=
      preparedExecStackWord (tr.cell t r) slot := by
  have ops:=prepared_control_opcode_exclusive tr t r pub localH (by omega) tag (by omega) chosen
  have op0 : tr.cell t r 466=0:=by simpa only [preparedControlOpcodeColumn,Nat.reduceLT,ite_true,Nat.reduceAdd,show ¬0=tag by omega,ite_false] using ops 0 (by decide)
  have op1 : tr.cell t r 467=0:=by simpa only [preparedControlOpcodeColumn,Nat.reduceLT,ite_true,Nat.reduceAdd,show ¬1=tag by omega,ite_false] using ops 1 (by decide)
  have op2 : tr.cell t r 468=0:=by simpa only [preparedControlOpcodeColumn,Nat.reduceLT,ite_true,Nat.reduceAdd,show ¬2=tag by omega,ite_false] using ops 2 (by decide)
  have br : tr.cell t r 606=0:=by simpa only [preparedControlOpcodeColumn,Nat.reduceLT,ite_false,Nat.reduceSub,Nat.reduceAdd,show ¬5=tag by omega] using ops 5 (by decide)
  have notTaken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [br];grind
  intro slot hs
  have limb (i : Nat) (hi : i<2) : preparedCodeLimb (tr.cell t (r+1)) (43+32*slot+16*i)=
      preparedCodeLimb (tr.cell t r) (43+32*slot+16*i) := by
    have member:=List.getElem_mem (l:=preparedControlLiteralExec) (n:=839+4*slot+2*i) (by change _<870;omega)
    rw [frame_stack_at ⟨slot,hs⟩ ⟨i,hi⟩] at member
    have h:=localH.constr r (by omega) _ member
    let push:=preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 466*tr.cell t r (32+slot))
    let write:=preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 467*((if slot+2≤8 then Expr.col (32+slot+2) false else .const 0).eval tr t r pub))
    let clear:=preparedExecGasSuccess.eval tr t r pub*((tr.cell t r 467+tr.cell t r 468+tr.cell t r 606)*tr.cell t r (32+slot+1))
    have pz : push=0 := by dsimp only [push];rw [op0];grind
    have wz : write=0 := by dsimp only [write];rw [op1];grind
    have ce : clear=0 := by
      dsimp only [clear];rw [op1,op2,br];grind
    change (if r+1=tr.height t then (0:Fp) else 1)*((preparedCodeBits (43+32*slot+16*i) true).eval tr t r pub+
      -(preparedControlTaken.eval tr t r pub*((preparedControlBelow slot).eval tr t r pub*
        (preparedCodeBits (43+32*slot+16*i)).eval tr t r pub)+
        ((1:Fp)+ -preparedControlTaken.eval tr t r pub)*
        (((1:Fp)+ -((push+write)+clear))*(preparedCodeBits (43+32*slot+16*i)).eval tr t r pub+
          (push*(preparedCodeBits (470+16*i)).eval tr t r pub+write*(preparedCodeBits (431+16*i)).eval tr t r pub))))=0 at h
    rw [if_neg (by omega),notTaken,pz,wz,ce,prepared_code_bits_eval,prepared_code_bits_eval] at h
    simp only [Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt nonlast] at h
    grind
  have low:=limb 0 (by decide)
  have high:=limb 1 (by decide)
  simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero] at low high
  rw [prepared_control_stack_word,prepared_control_stack_word,low,high]


/-- Block and end preserve the decoded stack height and its one-hot selector. -/
theorem prepared_control_frame_sp (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (tag : Nat) (mode : tag=3 ∨ tag=4)
    (chosen : tr.cell t r (preparedControlOpcodeColumn tag)=1) :
    ∃ sp,sp<9 ∧ (∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) ∧
      ∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=sp then 1 else 0 := by
  have ops:=prepared_control_opcode_exclusive tr t r pub localH (by omega) tag (by omega) chosen
  have op0 : tr.cell t r 466=0:=by simpa only [preparedControlOpcodeColumn,Nat.reduceLT,ite_true,Nat.reduceAdd,show ¬0=tag by omega,ite_false] using ops 0 (by decide)
  have op1 : tr.cell t r 467=0:=by simpa only [preparedControlOpcodeColumn,Nat.reduceLT,ite_true,Nat.reduceAdd,show ¬1=tag by omega,ite_false] using ops 1 (by decide)
  have op2 : tr.cell t r 468=0:=by simpa only [preparedControlOpcodeColumn,Nat.reduceLT,ite_true,Nat.reduceAdd,show ¬2=tag by omega,ite_false] using ops 2 (by decide)
  have br : tr.cell t r 606=0:=by simpa only [preparedControlOpcodeColumn,Nat.reduceLT,ite_false,Nat.reduceSub,Nat.reduceAdd,show ¬5=tag by omega] using ops 5 (by decide)

  obtain ⟨sp,bound,selected⟩:=prepared_control_literal_onehot tr t r pub localH (by omega)
  obtain ⟨nextSP,nextBound,nextSelected⟩:=prepared_control_literal_onehot tr t (r+1) pub localH nonlast
  have notTaken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [br];grind
  have delta : preparedControlDelta.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 466+ -((tr.cell t r 467+tr.cell t r 468)+tr.cell t r 606))=0
    rw [op0,op1,op2,br];grind
  have member : preparedControlSPStep∈preparedControlLiteralExecTable.constraints:=
    List.getElem_mem (l:=preparedControlLiteralExec) (n:=766) (by decide)
  have h:=localH.constr r (by omega) _ member
  change (if r+1=tr.height t then (0:Fp) else 1)*((preparedControlIndex 32 true).eval tr t r pub+
    -(preparedControlTaken.eval tr t r pub*(preparedControlIndex 640).eval tr t r pub+
      ((1:Fp)+ -preparedControlTaken.eval tr t r pub)*((preparedControlIndex 32).eval tr t r pub+preparedControlDelta.eval tr t r pub)))=0 at h
  rw [if_neg (by omega),notTaken,delta] at h
  have current : (preparedControlIndex 32).eval tr t r pub=Fp.ofNat sp:=
    prepared_control_index_selected (tr.cell t r) 32 sp bound selected
  have next : (preparedControlIndex 32 true).eval tr t r pub=Fp.ofNat nextSP := by
    have eq:=prepared_control_index_selected (tr.cell t (r+1)) 32 nextSP nextBound nextSelected
    simpa only [preparedControlIndex,preparedBalancedSum,Expr.eval,Expr.evalWith,rowEnv,
      instructionAddEnv,ite_true,Nat.mod_eq_of_lt nonlast,←Lean.Grind.Semiring.ofNat_eq_natCast,←Fp.ofNat_def] using eq
  rw [current,next] at h
  have fieldEq : Fp.ofNat nextSP=Fp.ofNat sp:=by grind
  have natEq:=congrArg Fp.toNat fieldEq
  simp only [Fp.toNat_ofNat] at natEq
  rw [Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega),Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega)] at natEq
  exact ⟨sp,bound,selected,by simpa only [natEq] using nextSelected⟩

end NearCompression
