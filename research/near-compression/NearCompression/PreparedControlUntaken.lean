import NearCompression.PreparedControlStack
import NearCompression.PreparedControlSequential

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm

theorem prepared_control_untaken_sp (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (zero : tr.cell t r 681=0) :
    ∃ sp,0<sp ∧ sp<9 ∧ (∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) ∧
      ∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=sp-1 then 1 else 0 := by
  have hr : r<tr.height t:=by omega
  have ops:=prepared_control_branch_opcode tr t r pub localH hr branch
  obtain ⟨sp,bound,selected⟩:=prepared_control_literal_onehot tr t r pub localH hr
  obtain ⟨nextSP,nextBound,nextSelected⟩:=prepared_control_literal_onehot tr t (r+1) pub localH nonlast
  have success : preparedExecGasSuccess.eval tr t r pub=1 := by
    change ((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430)=1
    rw [active,charged];grind
  have guardMember : preparedControlLiteralExec0769∈preparedControlLiteralExecTable.constraints:=
    List.getElem_mem (l:=preparedControlLiteralExec) (n:=769) (by decide)
  have guard:=localH.constr r hr _ guardMember
  change preparedExecGasSuccess.eval tr t r pub*((tr.cell t r 468+tr.cell t r 606)*tr.cell t r 32)+ -(0:Fp)=0 at guard
  rw [success,ops.1 2 (by decide),branch] at guard
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
  have delta : preparedControlDelta.eval tr t r pub= -(1:Fp) := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 466+ -((tr.cell t r 467+tr.cell t r 468)+tr.cell t r 606))= -(1:Fp)
    rw [success,ops.1 0 (by decide),ops.1 1 (by decide),ops.1 2 (by decide),branch];grind
  have member : preparedControlSPStep∈preparedControlLiteralExecTable.constraints:=
    List.getElem_mem (l:=preparedControlLiteralExec) (n:=766) (by decide)
  have h:=localH.constr r hr _ member
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
    preparedControlLiteralExec[839+4*slot.val+2*limb.val]'(by change _<870;omega)=
      preparedControlStackStep slot.val limb.val := by decide

/-- False br_if clears exactly the condition slot; every other encoded
stack word is unchanged. The next live height is separately proved above. -/
theorem prepared_control_untaken_stack (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (zero : tr.cell t r 681=0)
    (sp : Nat) (bound : sp<9) (selected : ∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    ∀ slot,slot<8 → preparedExecStackWord (tr.cell t (r+1)) slot=
      if slot+1=sp then 0 else preparedExecStackWord (tr.cell t r) slot := by
  have ops:=prepared_control_branch_opcode tr t r pub localH (by omega) branch
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
    have member:=List.getElem_mem (l:=preparedControlLiteralExec) (n:=839+4*slot+2*i) (by change _<870;omega)
    rw [untaken_stack_at ⟨slot,hs⟩ ⟨i,hi⟩] at member
    have h:=localH.constr r (by omega) _ member
    let push:=preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 466*tr.cell t r (32+slot))
    let write:=preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 467*((if slot+2≤8 then Expr.col (32+slot+2) false else .const 0).eval tr t r pub))
    let clear:=preparedExecGasSuccess.eval tr t r pub*((tr.cell t r 467+tr.cell t r 468+tr.cell t r 606)*tr.cell t r (32+slot+1))
    have pz : push=0 := by dsimp only [push];rw [ops.1 0 (by decide)];grind
    have wz : write=0 := by dsimp only [write];rw [ops.1 1 (by decide)];grind
    have ce : clear=tr.cell t r (32+(slot+1)) := by
      dsimp only [clear];rw [success,ops.1 1 (by decide),ops.1 2 (by decide),branch]
      rw [Nat.add_assoc];grind
    change (if r+1=tr.height t then (0:Fp) else 1)*((preparedCodeBits (43+32*slot+16*i) true).eval tr t r pub+
      -(preparedControlTaken.eval tr t r pub*((preparedControlBelow slot).eval tr t r pub*
        (preparedCodeBits (43+32*slot+16*i)).eval tr t r pub)+
        ((1:Fp)+ -preparedControlTaken.eval tr t r pub)*
        (((1:Fp)+ -((push+write)+clear))*(preparedCodeBits (43+32*slot+16*i)).eval tr t r pub+
          (push*(preparedCodeBits (470+16*i)).eval tr t r pub+write*(preparedCodeBits (431+16*i)).eval tr t r pub))))=0 at h
    rw [if_neg (by omega),notTaken,pz,wz,ce,selectedTop,prepared_code_bits_eval,prepared_code_bits_eval] at h
    simp only [Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt nonlast] at h
    split <;> grind
  have low:=limb 0 (by decide)
  have high:=limb 1 (by decide)
  simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero] at low high
  rw [prepared_control_stack_word,prepared_control_stack_word,low,high]
  split <;> rfl

theorem prepared_control_untaken_stack_projection (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (branch : tr.cell t r 606=1) (zero : tr.cell t r 681=0) :
    ∃ sp,0<sp ∧ sp<9 ∧ (∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) ∧
      (∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=sp-1 then 1 else 0) ∧
      preparedExecStackWord (tr.cell t r) (sp-1)=0 ∧
      ∀ slot,slot<8 → preparedExecStackWord (tr.cell t (r+1)) slot=
        if slot+1=sp then 0 else preparedExecStackWord (tr.cell t r) slot := by
  obtain ⟨sp,positive,bound,selected,nextSelected⟩:=prepared_control_untaken_sp tr t r pub localH nonlast active charged branch zero
  have condition:=prepared_control_condition_sound _ tr t r pub localH (by omega)
    prepared_control_literal_condition_source sp bound positive selected
  exact ⟨sp,positive,bound,selected,nextSelected,condition.2.mp zero,
    prepared_control_untaken_stack tr t r pub localH nonlast active charged branch zero sp bound selected⟩

end NearCompression
