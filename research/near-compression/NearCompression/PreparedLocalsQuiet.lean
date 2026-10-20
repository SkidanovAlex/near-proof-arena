import NearCompression.PreparedLocalsStack
import NearCompression.PreparedLocalsSequential
import NearCompression.PreparedLocalsDepth
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000 in
private theorem frame_stack_at : ∀ slot:Fin 8,∀ limb:Fin 2,
    preparedLocalsLiteralExecBase[1113+4*slot.val+2*limb.val]'(by change _<1144;omega)=
      preparedLocalsStackStep slot.val limb.val := by decide

/-- A zero success gate preserves every stack slot, including local-opcode rows. -/
theorem prepared_locals_quiet_stack (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (success : preparedExecGasSuccess.eval tr t r pub=0) :
    ∀ slot,slot<8 → preparedExecStackWord (tr.cell t (r+1)) slot=
      preparedExecStackWord (tr.cell t r) slot := by
  have notTaken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [success];grind
  intro slot hs
  have limb (i : Nat) (hi : i<2) : preparedCodeLimb (tr.cell t (r+1)) (43+32*slot+16*i)=
      preparedCodeLimb (tr.cell t r) (43+32*slot+16*i) := by
    have member:=List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1113+4*slot+2*i) (by change _<1144;omega)
    rw [frame_stack_at ⟨slot,hs⟩ ⟨i,hi⟩] at member
    have h:=localH.constr r (by omega) _ (prepared_locals_base_member count _ member)
    let push:=preparedExecGasSuccess.eval tr t r pub*((tr.cell t r 466+tr.cell t r 683)*tr.cell t r (32+slot))
    let write:=preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 467*((if slot+2≤8 then Expr.col (32+slot+2) false else .const 0).eval tr t r pub))
    let clear:=preparedExecGasSuccess.eval tr t r pub*((tr.cell t r 467+tr.cell t r 468+tr.cell t r 606+tr.cell t r 684)*tr.cell t r (32+slot+1))
    have pz : push=0 := by dsimp only [push];rw [success];grind
    have wz : write=0 := by dsimp only [write];rw [success];grind
    have ce : clear=0 := by
      dsimp only [clear];rw [success];grind
    change (if r+1=tr.height t then (0:Fp) else 1)*((preparedCodeBits (43+32*slot+16*i) true).eval tr t r pub+
      -(preparedControlTaken.eval tr t r pub*((preparedControlBelow slot).eval tr t r pub*
        (preparedCodeBits (43+32*slot+16*i)).eval tr t r pub)+
        ((1:Fp)+ -preparedControlTaken.eval tr t r pub)*
        (((1:Fp)+ -((push+write)+clear))*(preparedCodeBits (43+32*slot+16*i)).eval tr t r pub+
          (push*(tr.cell t r 466*(preparedCodeBits (470+16*i)).eval tr t r pub+tr.cell t r 683*(preparedLocalsRead i).eval tr t r pub)+write*(preparedCodeBits (431+16*i)).eval tr t r pub))))=0 at h
    rw [if_neg (by omega),notTaken,pz,wz,ce,prepared_code_bits_eval,prepared_code_bits_eval] at h
    simp only [Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt nonlast] at h
    grind
  have low:=limb 0 (by decide)
  have high:=limb 1 (by decide)
  simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero] at low high
  rw [prepared_control_stack_word,prepared_control_stack_word,low,high]


/-- A zero success gate preserves the decoded stack height. -/
theorem prepared_locals_quiet_sp (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (success : preparedExecGasSuccess.eval tr t r pub=0) :
    ∃ sp,sp<9 ∧ (∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) ∧
      ∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=sp then 1 else 0 := by
  obtain ⟨sp,bound,selected⟩:=prepared_locals_onehot count tr t r pub localH (by omega)
  obtain ⟨nextSP,nextBound,nextSelected⟩:=prepared_locals_onehot count tr t (r+1) pub localH nonlast
  have notTaken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [success];grind
  have delta : preparedLocalsDelta.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*((tr.cell t r 466+tr.cell t r 683)+ -(((tr.cell t r 467+tr.cell t r 468)+tr.cell t r 606)+tr.cell t r 684))=0
    rw [success];grind
  have member : preparedLocalsSPStep∈(preparedLocalsLiteralExecTable count).constraints:=
    prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1040) (by decide))
  have h:=localH.constr r (by omega) _ member
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
  have fieldEq : Fp.ofNat nextSP=Fp.ofNat sp:=by grind
  have natEq:=congrArg Fp.toNat fieldEq
  simp only [Fp.toNat_ofNat] at natEq
  rw [Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega),Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega)] at natEq
  exact ⟨sp,bound,selected,by simpa only [natEq] using nextSelected⟩

theorem prepared_locals_quiet (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (success : preparedExecGasSuccess.eval tr t r pub=0) :
    preparedCodeExecPC (tr.cell t (r+1))=preparedCodeExecPC (tr.cell t r) ∧
    (∀ i,i<9 → tr.cell t (r+1) (32+i)=tr.cell t r (32+i)) ∧
    (∀ slot,slot<8 → preparedExecStackWord (tr.cell t (r+1)) slot=preparedExecStackWord (tr.cell t r) slot) := by
  have taken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*_=0
    rw [success];grind
  have advance : preparedControlAdvance.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*_=0
    rw [success];grind
  have pc:=prepared_locals_sequential_pc count tr t r pub localH nonlast taken 0 (by decide) advance
  obtain ⟨sp,hs,selected,nextSelected⟩:=prepared_locals_quiet_sp count tr t r pub localH nonlast success
  refine ⟨by simpa using pc,?_,prepared_locals_quiet_stack count tr t r pub localH nonlast success⟩
  intro i hi
  rw [selected i hi,nextSelected i hi]
end NearCompression
