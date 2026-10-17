import NearCompression.PreparedTypedOpcode
import NearCompression.PreparedControlSequential
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem at_819 : ∀count:Fin 5,(preparedTypedLiteralExec count)[1285]?=some preparedLocalsLiteralExec0819 := by decide
private theorem at_1002 : ∀count:Fin 5,(preparedTypedLiteralExec count)[1623+66*(4-count.val)]?=some preparedLocalsLiteralExec1002 := by decide
private theorem at_1003 : ∀count:Fin 5,(preparedTypedLiteralExec count)[1624+66*(4-count.val)]?=some preparedLocalsLiteralExec1003 := by decide
private theorem at_1004 : ∀count:Fin 5,(preparedTypedLiteralExec count)[1625+66*(4-count.val)]?=some preparedControlPCStepLow := by decide
private theorem at_1005 : ∀count:Fin 5,(preparedTypedLiteralExec count)[1626+66*(4-count.val)]?=some preparedControlPCStepHigh := by decide
private theorem at_1047 : ∀count:Fin 5,(preparedTypedLiteralExec count)[1668+66*(4-count.val)]?=some preparedControlLabelStep := by decide
private theorem heights_at : ∀count:Fin 5,∀i:Fin 9,(preparedTypedLiteralExec count)[1669+66*(4-count.val)+i.val]?=some (preparedControlHeightStep i) := by decide
private theorem targets_at : ∀count:Fin 5,∀i:Fin 2,(preparedTypedLiteralExec count)[1678+66*(4-count.val)+2*i.val]?=some (preparedControlTargetStep i) := by decide

theorem prepared_typed_literal_limb (count : Nat) (hc : count≤4) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (base : Nat) (fits : base+16≤682) : (preparedCodeLimb (tr.cell t r) base).toNat<65536 := by
  exact instruction_bit_expr_bound _ 16 base (by decide) (fun i hi=>
    prepared_typed_source_boolean count hc tr t r pub localH hr _ (by omega) (by omega) (by omega))

/-- Outside a taken branch, the actual PC equations enforce bounded natural
addition by the derived advance flag, including no high-limb overflow. -/
theorem prepared_typed_sequential_pc (count : Nat) (hc : count≤4) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (notTaken : preparedControlTaken.eval tr t r pub=0)
    (step : Nat) (stepBound : step≤1) (advance : preparedControlAdvance.eval tr t r pub=Fp.ofNat step) :
    preparedCodeExecPC (tr.cell t (r+1))=preparedCodeExecPC (tr.cell t r)+step := by
  have lowMember : preparedControlPCStepLow∈(preparedTypedLiteralExecTable count).constraints:=
    List.mem_of_getElem? (at_1004 ⟨count,by omega⟩)
  have highMember : preparedControlPCStepHigh∈(preparedTypedLiteralExecTable count).constraints:=
    List.mem_of_getElem? (at_1005 ⟨count,by omega⟩)
  have low:=localH.constr r (by omega) _ lowMember
  have high:=localH.constr r (by omega) _ highMember
  change ((if r+1=tr.height t then (0:Fp) else 1)*((1:Fp)+ -preparedControlTaken.eval tr t r pub))*
    ((preparedCodeBits 0).eval tr t r pub+preparedControlAdvance.eval tr t r pub+
      -((preparedCodeBits 0 true).eval tr t r pub+65536*tr.cell t r 465))=0 at low
  change ((if r+1=tr.height t then (0:Fp) else 1)*((1:Fp)+ -preparedControlTaken.eval tr t r pub))*
    ((preparedCodeBits 16 true).eval tr t r pub+ -((preparedCodeBits 16).eval tr t r pub+tr.cell t r 465))=0 at high
  rw [if_neg (by omega),notTaken,advance] at low
  rw [if_neg (by omega),notTaken] at high
  rw [prepared_code_bits_eval,prepared_code_bits_eval] at low high
  simp only [Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt nonlast] at low high
  have lo : preparedCodeLimb (tr.cell t r) 0+Fp.ofNat step+0=
      preparedCodeLimb (tr.cell t (r+1)) 0+65536*tr.cell t r 465 := by grind
  have hi : preparedCodeLimb (tr.cell t r) 16+(0:Fp)+tr.cell t r 465=
      preparedCodeLimb (tr.cell t (r+1)) 16+65536*(0:Fp) := by grind
  have carry:=prepared_typed_source_boolean count hc tr t r pub localH (by omega) 465 (by decide) (by decide) (by decide)
  have sn : (Fp.ofNat step).toNat=step := by
    rw [Fp.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega)
  have l:=instruction_add_limb_sound _ (Fp.ofNat step) 0 _ _
    (prepared_typed_literal_limb count hc tr t r pub localH (by omega) 0 (by decide))
    (by rw [sn];omega) (by decide)
    (prepared_typed_literal_limb count hc tr t (r+1) pub localH nonlast 0 (by decide)) carry lo
  have h:=instruction_add_limb_sound _ 0 _ _ 0
    (prepared_typed_literal_limb count hc tr t r pub localH (by omega) 16 (by decide)) (by decide)
    carry (prepared_typed_literal_limb count hc tr t (r+1) pub localH nonlast 16 (by decide)) (by decide) hi
  change (preparedCodeLimb (tr.cell t r) 0).toNat+(Fp.ofNat step).toNat+0=
    (preparedCodeLimb (tr.cell t (r+1)) 0).toNat+65536*(tr.cell t r 465).toNat at l
  change (preparedCodeLimb (tr.cell t r) 16).toNat+0+(tr.cell t r 465).toNat=
    (preparedCodeLimb (tr.cell t (r+1)) 16).toNat+65536*0 at h
  rw [sn] at l
  unfold preparedCodeExecPC
  omega

/-- Successful non-returning control instructions keep execution active.
The current failure flag is constrained by the literal failure invariant. -/
theorem prepared_typed_continue_status (count : Nat) (hc : count≤4) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (notReturn : tr.cell t r 469*((1:Fp)+ -tr.cell t r 639)=0) :
    tr.cell t r 42=0 ∧ tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have im : preparedLocalsLiteralExec0819∈(preparedTypedLiteralExecTable count).constraints:=
    List.mem_of_getElem? (at_819 ⟨count,by omega⟩)
  have dm : preparedLocalsLiteralExec1002∈(preparedTypedLiteralExecTable count).constraints:=
    List.mem_of_getElem? (at_1002 ⟨count,by omega⟩)
  have fm : preparedLocalsLiteralExec1003∈(preparedTypedLiteralExecTable count).constraints:=
    List.mem_of_getElem? (at_1003 ⟨count,by omega⟩)
  have inv:=localH.constr r (by omega) _ im
  have done:=localH.constr r (by omega) _ dm
  have fail:=localH.constr r (by omega) _ fm
  change tr.cell t r 42*((1:Fp)+ -tr.cell t r 41)+ -(0:Fp)=0 at inv
  change (if r+1=tr.height t then (0:Fp) else 1)*(tr.cell t ((r+1)%tr.height t) 41+
    -(tr.cell t r 41+(((1:Fp)+ -tr.cell t r 41)*tr.cell t r 430+
      (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*(tr.cell t r 469*((1:Fp)+ -tr.cell t r 639)))))=0 at done
  change (if r+1=tr.height t then (0:Fp) else 1)*(tr.cell t ((r+1)%tr.height t) 42+
    -(tr.cell t r 42+((1:Fp)+ -tr.cell t r 41)*tr.cell t r 430))=0 at fail
  rw [active] at inv
  rw [if_neg (by omega),Nat.mod_eq_of_lt nonlast,active,charged,notReturn] at done
  rw [if_neg (by omega),Nat.mod_eq_of_lt nonlast,active,charged] at fail
  grind

/-- All label-state equations extracted from the literal table, reusable
for opening, retaining and removing a label. -/
theorem prepared_typed_label_equations (count : Nat) (hc : count≤4) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t) :
    tr.cell t (r+1) 639=preparedControlOpened.eval tr t r pub+preparedControlKeep.eval tr t r pub*tr.cell t r 639 ∧
    (∀ i,i<9 → tr.cell t (r+1) (640+i)=preparedControlOpened.eval tr t r pub*tr.cell t r (32+i)+
      preparedControlKeep.eval tr t r pub*tr.cell t r (640+i)) ∧
    ∀ i,i<2 → preparedCodeLimb (tr.cell t (r+1)) (649+16*i)=
      preparedControlOpened.eval tr t r pub*preparedCodeLimb (tr.cell t r) (607+16*i)+
      preparedControlKeep.eval tr t r pub*preparedCodeLimb (tr.cell t r) (649+16*i) := by
  have trans : (if r+1=tr.height t then (0:Fp) else 1)=1:=if_neg (by omega)
  refine ⟨?_,?_,?_⟩
  · have member : preparedControlLabelStep∈(preparedTypedLiteralExecTable count).constraints :=
      List.mem_of_getElem? (at_1047 ⟨count,by omega⟩)
    have h:=localH.constr r (by omega) _ member
    change (if r+1=tr.height t then (0:Fp) else 1)*(tr.cell t ((r+1)%tr.height t) 639+
      -(preparedControlOpened.eval tr t r pub+preparedControlKeep.eval tr t r pub*tr.cell t r 639))=0 at h
    rw [trans,Nat.mod_eq_of_lt nonlast] at h
    grind
  · intro i hi
    have h:=localH.constr r (by omega) _ (List.mem_of_getElem? (heights_at ⟨count,by omega⟩ ⟨i,hi⟩))
    change (if r+1=tr.height t then (0:Fp) else 1)*(tr.cell t ((r+1)%tr.height t) (640+i)+
      -(preparedControlOpened.eval tr t r pub*tr.cell t r (32+i)+preparedControlKeep.eval tr t r pub*tr.cell t r (640+i)))=0 at h
    rw [trans,Nat.mod_eq_of_lt nonlast] at h
    grind
  · intro i hi
    have h:=localH.constr r (by omega) _ (List.mem_of_getElem? (targets_at ⟨count,by omega⟩ ⟨i,hi⟩))
    change (if r+1=tr.height t then (0:Fp) else 1)*((preparedCodeBits (649+16*i) true).eval tr t r pub+
      -(preparedControlOpened.eval tr t r pub*(preparedCodeBits (607+16*i)).eval tr t r pub+
        preparedControlKeep.eval tr t r pub*(preparedCodeBits (649+16*i)).eval tr t r pub))=0 at h
    rw [trans,prepared_code_bits_eval,prepared_code_bits_eval,prepared_code_bits_eval] at h
    simp only [Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt nonlast] at h
    grind


/-- Non-control instructions advance PC and preserve label state. Opcode exclusions
are explicit here and can be derived from authenticated CODE. -/
theorem prepared_typed_pc_label (count : Nat) (hc : count≤4) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (notEnd : tr.cell t r 469=0) (notBlock : tr.cell t r 605=0) (notBranch : tr.cell t r 606=0) :
    preparedCodeExecPC (tr.cell t (r+1))=preparedCodeExecPC (tr.cell t r)+1 ∧
    tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 ∧
    tr.cell t (r+1) 639=tr.cell t r 639 ∧
    (∀ i,i<9 → tr.cell t (r+1) (640+i)=tr.cell t r (640+i)) ∧
    preparedControlSavedTarget (tr.cell t (r+1))=preparedControlSavedTarget (tr.cell t r) := by
  have notTaken : preparedControlTaken.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 606*tr.cell t r 681)=0
    rw [notBranch];grind
  have advance : preparedControlAdvance.eval tr t r pub=Fp.ofNat 1 := by
    change (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*
      ((1:Fp)+ -(tr.cell t r 469*((1:Fp)+ -tr.cell t r 639)+tr.cell t r 606*tr.cell t r 681))=1
    rw [active,charged,notEnd,notBranch];grind
  have status:=prepared_typed_continue_status count hc tr t r pub localH nonlast active charged (by rw [notEnd];grind)
  have opened : preparedControlOpened.eval tr t r pub=0 := by
    change preparedExecGasSuccess.eval tr t r pub*tr.cell t r 605=0
    rw [notBlock];grind
  have keep : preparedControlKeep.eval tr t r pub=1 := by
    change (1:Fp)+ -(preparedControlOpened.eval tr t r pub+
      (preparedControlTaken.eval tr t r pub+preparedExecGasSuccess.eval tr t r pub*(tr.cell t r 469*tr.cell t r 639)))=1
    rw [opened,notTaken,notEnd];grind
  have labels:=prepared_typed_label_equations count hc tr t r pub localH nonlast
  rw [opened,keep] at labels
  refine ⟨prepared_typed_sequential_pc count hc tr t r pub localH nonlast notTaken 1 (by decide) advance,
    status.2.1,status.2.2,by grind,?_,?_⟩
  · intro i hi;have h:=labels.2.1 i hi;grind
  · have low:=labels.2.2 0 (by decide)
    have high:=labels.2.2 1 (by decide)
    have l : preparedCodeLimb (tr.cell t (r+1)) 649=preparedCodeLimb (tr.cell t r) 649:=by simpa only [Nat.mul_zero,Nat.add_zero] using (show _=_ from by grind)
    have h : preparedCodeLimb (tr.cell t (r+1)) 665=preparedCodeLimb (tr.cell t r) 665:=by simpa only [Nat.mul_one,Nat.reduceAdd] using (show _=_ from by grind)
    unfold preparedControlSavedTarget
    rw [l,h]

end NearCompression
