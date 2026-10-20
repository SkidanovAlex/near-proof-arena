import NearCompression.PreparedControlCondition

set_option maxRecDepth 65536
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

/-- Gas equations do not require a sequential-PC constraint. This source
interface works for both taken jumps and sequential execution. -/
structure PreparedControlGasSource (table : Table) : Prop where
  boolean : ∀ i,i<682 → preparedGasBoolean i∈table.constraints
  subtract : ∀ i,i<4 → preparedExecGasSubtract i∈table.constraints
  update : ∀ i,i<4 → preparedExecGasUpdate i∈table.constraints

theorem prepared_control_gas_boolean (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (source : PreparedControlGasSource table) (localH : TableLocal table tr t pub)
    (r : Nat) (hr : r<tr.height t) (i : Nat) (hi : i<682) : (tr.cell t r i).toNat≤1 := by
  have h:=localH.constr r hr _ (source.boolean i hi)
  change tr.cell t r i*(tr.cell t r i+ -(1:Fp))+ -(0:Fp)=0 at h
  apply instruction_add_boolean_bound
  grind

theorem prepared_control_gas_limb_bound (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (source : PreparedControlGasSource table) (localH : TableLocal table tr t pub)
    (r : Nat) (hr : r<tr.height t) (base : Nat) (fits : base+16≤682) :
    (preparedCodeLimb (tr.cell t r) base).toNat<65536 := by
  exact instruction_bit_expr_bound _ 16 base (by decide) (fun k hk=>
    prepared_control_gas_boolean table tr t pub source localH r hr _ (by omega))

theorem prepared_control_gas_equation (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (source : PreparedControlGasSource table) (localH : TableLocal table tr t pub)
    (hr : r<tr.height t) (i : Nat) (hi : i<4) :
    (preparedCodeLimb (tr.cell t r) (363+16*i)).toNat+
      (preparedCodeLimb (tr.cell t r) (502+16*i)).toNat+
      (if i=0 then 0 else (tr.cell t r (427+(i-1))).toNat)=
    (preparedCodeLimb (tr.cell t r) (299+16*i)).toNat+65536*(tr.cell t r (427+i)).toNat := by
  have h:=localH.constr r hr _ (source.subtract i hi)
  have gb:=prepared_control_gas_limb_bound table tr t pub source localH r hr (299+16*i) (by omega)
  have fb:=prepared_control_gas_limb_bound table tr t pub source localH r hr (502+16*i) (by omega)
  have db:=prepared_control_gas_limb_bound table tr t pub source localH r hr (363+16*i) (by omega)
  have cb:=prepared_control_gas_boolean table tr t pub source localH r hr (427+i) (by omega)
  by_cases zero : i=0
  · subst i
    change (preparedCodeBits 299).eval tr t r pub+ -(preparedCodeBits 502).eval tr t r pub+ -(0:Fp)+
      -((preparedCodeBits 363).eval tr t r pub+ -(65536*tr.cell t r 427))=0 at h
    rw [prepared_code_bits_eval,prepared_code_bits_eval,prepared_code_bits_eval] at h
    have eq : preparedCodeLimb (tr.cell t r) 363+preparedCodeLimb (tr.cell t r) 502+(0:Fp)=
      preparedCodeLimb (tr.cell t r) 299+65536*tr.cell t r 427 := by grind
    exact instruction_add_limb_sound _ _ 0 _ _ db fb (by decide) gb cb eq
  · have pb:=prepared_control_gas_boolean table tr t pub source localH r hr (427+(i-1)) (by omega)
    have idx : 427+i-1=427+(i-1):=by omega
    simp only [preparedExecGasSubtract,ite_eq_right zero,Expr.eval,Expr.evalWith] at h
    change (preparedCodeBits (299+16*i)).eval tr t r pub+
      -(preparedCodeBits (502+16*i)).eval tr t r pub+ -tr.cell t r (427+i-1)+
      -((preparedCodeBits (363+16*i)).eval tr t r pub+ -(65536*tr.cell t r (427+i)))=0 at h
    rw [prepared_code_bits_eval,prepared_code_bits_eval,prepared_code_bits_eval,idx] at h
    have eq : preparedCodeLimb (tr.cell t r) (363+16*i)+preparedCodeLimb (tr.cell t r) (502+16*i)+
        tr.cell t r (427+(i-1))=preparedCodeLimb (tr.cell t r) (299+16*i)+65536*tr.cell t r (427+i) := by grind
    simpa only [ite_eq_right zero] using instruction_add_limb_sound _ _ _ _ _ db fb pb gb cb eq

theorem prepared_control_gas_borrow (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (source : PreparedControlGasSource table) (localH : TableLocal table tr t pub)
    (hr : r<tr.height t) :
    ((tr.cell t r 430).toNat=1 ↔ preparedExecWord64 (tr.cell t r) 299<preparedExecWord64 (tr.cell t r) 502) ∧
    ((tr.cell t r 430).toNat=0 ↔ preparedExecWord64 (tr.cell t r) 502≤preparedExecWord64 (tr.cell t r) 299) ∧
    preparedExecWord64 (tr.cell t r) 363=
      (preparedExecWord64 (tr.cell t r) 299+18446744073709551616-preparedExecWord64 (tr.cell t r) 502)%18446744073709551616 := by
  apply prepared_gas_nat_borrow (fun i=>(preparedCodeLimb (tr.cell t r) (299+16*i)).toNat)
    (fun i=>(preparedCodeLimb (tr.cell t r) (502+16*i)).toNat)
    (fun i=>(preparedCodeLimb (tr.cell t r) (363+16*i)).toNat)
    (fun i=>(tr.cell t r (427+i)).toNat)
  · intro i hi;exact prepared_control_gas_limb_bound table tr t pub source localH r hr _ (by omega)
  · intro i hi;exact prepared_control_gas_limb_bound table tr t pub source localH r hr _ (by omega)
  · intro i hi;exact prepared_control_gas_limb_bound table tr t pub source localH r hr _ (by omega)
  · exact prepared_control_gas_boolean table tr t pub source localH r hr 430 (by decide)
  · exact prepared_control_gas_equation table tr t r pub source localH hr

theorem prepared_control_gas_update_word (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (source : PreparedControlGasSource table) (localH : TableLocal table tr t pub)
    (nonlast : r+1<tr.height t) (successful : Bool)
    (flag : preparedExecGasSuccess.eval tr t r pub=if successful then 1 else 0) :
    preparedExecWord64 (tr.cell t (r+1)) 299=
      preparedExecWord64 (tr.cell t r) (if successful then 363 else 299) := by
  have limbs (i : Nat) (hi : i<4) :
      preparedCodeLimb (tr.cell t (r+1)) (299+16*i)=
        preparedCodeLimb (tr.cell t r) ((if successful then 363 else 299)+16*i) := by
    have h:=localH.constr r (by omega) _ (source.update i hi)
    change (if r+1=tr.height t then (0:Fp) else 1)*
      ((preparedCodeBits (299+16*i) true).eval tr t r pub+
      -(preparedExecGasSuccess.eval tr t r pub*(preparedCodeBits (363+16*i)).eval tr t r pub+
        ((1:Fp)+ -preparedExecGasSuccess.eval tr t r pub)*(preparedCodeBits (299+16*i)).eval tr t r pub))=0 at h
    rw [ite_eq_right (by omega),flag,prepared_code_bits_eval,prepared_code_bits_eval,prepared_code_bits_eval] at h
    simp only [Bool.false_eq_true,ite_true,ite_false,Nat.mod_eq_of_lt nonlast] at h
    cases successful <;> simp only [Bool.false_eq_true,ite_true,ite_false] at h ⊢ <;> grind
  simp only [preparedExecWord64,preparedGasWord]
  rw [limbs 0 (by decide),limbs 1 (by decide),limbs 2 (by decide),limbs 3 (by decide)]

theorem prepared_control_gas_success (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (source : PreparedControlGasSource table) (localH : TableLocal table tr t pub)
    (nonlast : r+1<tr.height t) (active : tr.cell t r 41=0)
    (enough : preparedExecWord64 (tr.cell t r) 502≤preparedExecWord64 (tr.cell t r) 299) :
    tr.cell t r 430=0 ∧
    preparedExecWord64 (tr.cell t (r+1)) 299=
      preparedExecWord64 (tr.cell t r) 299-preparedExecWord64 (tr.cell t r) 502 := by
  have borrow:=prepared_control_gas_borrow table tr t r pub source localH (by omega)
  have zero : tr.cell t r 430=0 := by
    apply Fp.ext
    exact borrow.2.1.mpr enough
  have flag : preparedExecGasSuccess.eval tr t r pub=1 := by
    change ((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430)=1
    rw [active,zero];grind
  have update:=prepared_control_gas_update_word table tr t r pub source localH nonlast true flag
  have gasBound : preparedExecWord64 (tr.cell t r) 299<18446744073709551616 :=
    prepared_gas_word_bound _ (fun i hi=>prepared_control_gas_limb_bound table tr t pub source localH r (by omega) _ (by omega))
  refine ⟨zero,?_⟩
  change preparedExecWord64 (tr.cell t (r+1)) 299=preparedExecWord64 (tr.cell t r) 363 at update
  rw [update,borrow.2.2]
  have eq : preparedExecWord64 (tr.cell t r) 299+18446744073709551616-preparedExecWord64 (tr.cell t r) 502=
      (preparedExecWord64 (tr.cell t r) 299-preparedExecWord64 (tr.cell t r) 502)+18446744073709551616 := by omega
  rw [eq,Nat.add_mod]
  simp only [Nat.mod_self,Nat.add_zero,Nat.mod_eq_of_lt (show preparedExecWord64 (tr.cell t r) 299-preparedExecWord64 (tr.cell t r) 502<18446744073709551616 by omega)]

theorem prepared_control_gas_exhaustion (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (source : PreparedControlGasSource table) (localH : TableLocal table tr t pub)
    (nonlast : r+1<tr.height t)
    (insufficient : preparedExecWord64 (tr.cell t r) 299<preparedExecWord64 (tr.cell t r) 502) :
    tr.cell t r 430=1 ∧ preparedExecWord64 (tr.cell t (r+1)) 299=preparedExecWord64 (tr.cell t r) 299 := by
  have borrow:=prepared_control_gas_borrow table tr t r pub source localH (by omega)
  have one : tr.cell t r 430=1 := by
    apply Fp.ext
    exact borrow.1.mpr insufficient
  refine ⟨one,?_⟩
  apply prepared_control_gas_update_word table tr t r pub source localH nonlast false
  change ((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430)=0
  rw [one];grind

private theorem control_subtract_at : ∀ i:Fin 4,
    preparedControlLiteralExec[724+i.val]'(by change _<870;omega)=preparedExecGasSubtract i.val := by decide
private theorem control_gas_update_at : ∀ i:Fin 4,
    preparedControlLiteralExec[832+i.val]'(by change _<870;omega)=preparedExecGasUpdate i.val := by decide

theorem prepared_control_literal_gas_source : PreparedControlGasSource preparedControlLiteralExecTable := by
  refine ⟨prepared_control_literal_condition_source.boolean,?_,?_⟩
  · intro i hi
    have h:=List.getElem_mem (l:=preparedControlLiteralExec) (n:=724+i) (by change _<870;omega)
    rw [control_subtract_at ⟨i,hi⟩] at h
    exact h
  · intro i hi
    have h:=List.getElem_mem (l:=preparedControlLiteralExec) (n:=832+i) (by change _<870;omega)
    rw [control_gas_update_at ⟨i,hi⟩] at h
    exact h

end NearCompression
