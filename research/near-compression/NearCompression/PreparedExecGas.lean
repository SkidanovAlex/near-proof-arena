import NearCompression.PreparedExecPC

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

def preparedExecWord64 (row : Nat → Fp) (base : Nat) : Nat :=
  preparedGasWord (fun i=>(preparedCodeLimb row (base+16*i)).toNat)
def preparedExecGasSubtract (i : Nat) : Expr :=
  .add (.add (.add (preparedCodeBits (299+16*i)) (.neg (preparedCodeBits (502+16*i))))
      (.neg (if i=0 then .const 0 else .col (427+i-1) false)))
    (.neg (.add (preparedCodeBits (363+16*i))
      (.neg (.mul (.const 65536) (.col (427+i) false)))))
def preparedExecGasSuccess : Expr :=
  .mul (.add (.const 1) (.neg (.col 41 false))) (.add (.const 1) (.neg (.col 430 false)))
def preparedExecGasUpdate (i : Nat) : Expr :=
  .mul .isTransition (.add (preparedCodeBits (299+16*i) true)
    (.neg (.add (.mul preparedExecGasSuccess (preparedCodeBits (363+16*i)))
      (.mul (.add (.const 1) (.neg preparedExecGasSuccess)) (preparedCodeBits (299+16*i))))))

structure PreparedExecGasSource (table : Table) : Prop where
  pc : PreparedExecPCSource table
  subtract : ∀ i,i<4 → preparedExecGasSubtract i∈table.constraints
  update : ∀ i,i<4 → preparedExecGasUpdate i∈table.constraints

theorem prepared_exec_gas_equation (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (source : PreparedExecGasSource table) (localH : TableLocal table tr t pub)
    (hr : r<tr.height t) (i : Nat) (hi : i<4) :
    (preparedCodeLimb (tr.cell t r) (363+16*i)).toNat+
      (preparedCodeLimb (tr.cell t r) (502+16*i)).toNat+
      (if i=0 then 0 else (tr.cell t r (427+(i-1))).toNat)=
    (preparedCodeLimb (tr.cell t r) (299+16*i)).toNat+65536*(tr.cell t r (427+i)).toNat := by
  have h:=localH.constr r hr _ (source.subtract i hi)
  have gb:=prepared_exec_limb_bound table tr t pub source.pc localH r hr (299+16*i) (by omega)
  have fb:=prepared_exec_limb_bound table tr t pub source.pc localH r hr (502+16*i) (by omega)
  have db:=prepared_exec_limb_bound table tr t pub source.pc localH r hr (363+16*i) (by omega)
  have cb:=prepared_exec_boolean table tr t pub source.pc localH r hr (427+i) (by omega)
  by_cases zero : i=0
  · subst i
    change (preparedCodeBits 299).eval tr t r pub+ -(preparedCodeBits 502).eval tr t r pub+ -(0:Fp)+
      -((preparedCodeBits 363).eval tr t r pub+ -(65536*tr.cell t r 427))=0 at h
    rw [prepared_code_bits_eval,prepared_code_bits_eval,prepared_code_bits_eval] at h
    have eq : preparedCodeLimb (tr.cell t r) 363+preparedCodeLimb (tr.cell t r) 502+(0:Fp)=
      preparedCodeLimb (tr.cell t r) 299+65536*tr.cell t r 427 := by grind
    exact instruction_add_limb_sound _ _ 0 _ _ db fb (by decide) gb cb eq
  · have pb:=prepared_exec_boolean table tr t pub source.pc localH r hr (427+(i-1)) (by omega)
    have idx : 427+i-1=427+(i-1):=by omega
    simp only [preparedExecGasSubtract,ite_eq_right zero,Expr.eval,Expr.evalWith] at h
    change (preparedCodeBits (299+16*i)).eval tr t r pub+
      -(preparedCodeBits (502+16*i)).eval tr t r pub+ -tr.cell t r (427+i-1)+
      -((preparedCodeBits (363+16*i)).eval tr t r pub+ -(65536*tr.cell t r (427+i)))=0 at h
    rw [prepared_code_bits_eval,prepared_code_bits_eval,prepared_code_bits_eval,idx] at h
    have eq : preparedCodeLimb (tr.cell t r) (363+16*i)+preparedCodeLimb (tr.cell t r) (502+16*i)+
        tr.cell t r (427+(i-1))=preparedCodeLimb (tr.cell t r) (299+16*i)+65536*tr.cell t r (427+i) := by grind
    simpa only [ite_eq_right zero] using instruction_add_limb_sound _ _ _ _ _ db fb pb gb cb eq

theorem prepared_exec_gas_borrow (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (source : PreparedExecGasSource table) (localH : TableLocal table tr t pub)
    (hr : r<tr.height t) :
    ((tr.cell t r 430).toNat=1 ↔ preparedExecWord64 (tr.cell t r) 299<preparedExecWord64 (tr.cell t r) 502) ∧
    ((tr.cell t r 430).toNat=0 ↔ preparedExecWord64 (tr.cell t r) 502≤preparedExecWord64 (tr.cell t r) 299) ∧
    preparedExecWord64 (tr.cell t r) 363=
      (preparedExecWord64 (tr.cell t r) 299+18446744073709551616-preparedExecWord64 (tr.cell t r) 502)%18446744073709551616 := by
  apply prepared_gas_nat_borrow (fun i=>(preparedCodeLimb (tr.cell t r) (299+16*i)).toNat)
    (fun i=>(preparedCodeLimb (tr.cell t r) (502+16*i)).toNat)
    (fun i=>(preparedCodeLimb (tr.cell t r) (363+16*i)).toNat)
    (fun i=>(tr.cell t r (427+i)).toNat)
  · intro i hi;exact prepared_exec_limb_bound table tr t pub source.pc localH r hr _ (by omega)
  · intro i hi;exact prepared_exec_limb_bound table tr t pub source.pc localH r hr _ (by omega)
  · intro i hi;exact prepared_exec_limb_bound table tr t pub source.pc localH r hr _ (by omega)
  · exact prepared_exec_boolean table tr t pub source.pc localH r hr 430 (by decide)
  · exact prepared_exec_gas_equation table tr t r pub source localH hr

theorem prepared_exec_gas_update_word (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (source : PreparedExecGasSource table) (localH : TableLocal table tr t pub)
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

theorem prepared_exec_gas_success (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (source : PreparedExecGasSource table) (localH : TableLocal table tr t pub)
    (nonlast : r+1<tr.height t) (active : tr.cell t r 41=0)
    (enough : preparedExecWord64 (tr.cell t r) 502≤preparedExecWord64 (tr.cell t r) 299) :
    tr.cell t r 430=0 ∧
    preparedExecWord64 (tr.cell t (r+1)) 299=
      preparedExecWord64 (tr.cell t r) 299-preparedExecWord64 (tr.cell t r) 502 := by
  have borrow:=prepared_exec_gas_borrow table tr t r pub source localH (by omega)
  have zero : tr.cell t r 430=0 := by
    apply Fp.ext
    exact borrow.2.1.mpr enough
  have flag : preparedExecGasSuccess.eval tr t r pub=1 := by
    change ((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430)=1
    rw [active,zero];grind
  have update:=prepared_exec_gas_update_word table tr t r pub source localH nonlast true flag
  have gasBound : preparedExecWord64 (tr.cell t r) 299<18446744073709551616 :=
    prepared_gas_word_bound _ (fun i hi=>prepared_exec_limb_bound table tr t pub source.pc localH r (by omega) _ (by omega))
  refine ⟨zero,?_⟩
  change preparedExecWord64 (tr.cell t (r+1)) 299=preparedExecWord64 (tr.cell t r) 363 at update
  rw [update,borrow.2.2]
  have eq : preparedExecWord64 (tr.cell t r) 299+18446744073709551616-preparedExecWord64 (tr.cell t r) 502=
      (preparedExecWord64 (tr.cell t r) 299-preparedExecWord64 (tr.cell t r) 502)+18446744073709551616 := by omega
  rw [eq,Nat.add_mod]
  simp only [Nat.mod_self,Nat.add_zero,Nat.mod_eq_of_lt (show preparedExecWord64 (tr.cell t r) 299-preparedExecWord64 (tr.cell t r) 502<18446744073709551616 by omega)]

theorem prepared_exec_gas_exhaustion (table : Table) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (source : PreparedExecGasSource table) (localH : TableLocal table tr t pub)
    (nonlast : r+1<tr.height t)
    (insufficient : preparedExecWord64 (tr.cell t r) 299<preparedExecWord64 (tr.cell t r) 502) :
    tr.cell t r 430=1 ∧ preparedExecWord64 (tr.cell t (r+1)) 299=preparedExecWord64 (tr.cell t r) 299 := by
  have borrow:=prepared_exec_gas_borrow table tr t r pub source localH (by omega)
  have one : tr.cell t r 430=1 := by
    apply Fp.ext
    exact borrow.1.mpr insufficient
  refine ⟨one,?_⟩
  apply prepared_exec_gas_update_word table tr t r pub source localH nonlast false
  change ((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430)=0
  rw [one];grind

/-- Authenticated descriptor limbs reconstruct the actual prepared range fee;
there is no independent selected-fee bound or fee-equality assumption. -/
theorem prepared_exec_authenticated_fee (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedCodeBusAir ec cc boundary count) pub tr)
    (source : PreparedCodeOrderSource (preparedCodeDataTable cc))
    (inactive : ∀ i,i<25 → preparedCodeInactive (172+i)∈cc)
    (pf : PFunc) (fn : Nat) (checked : preparedCodeVariableCheck pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) :
    let pc:=preparedCodeExecPC (tr.cell 0 r)
    pc<pf.code.size ∧ PreparedWasmCharge pf pc (preparedExecWord64 (tr.cell 0 r) 502) ∧
      preparedExecWord64 (tr.cell 0 r) 502<u64Bound := by
  obtain ⟨live,op,fee,amount,code,gas,inspect,bound,charge,fields⟩:=
    prepared_code_variable_fetch ec cc boundary count tr pub holds source inactive pf fn checked r hr
  have limbs (i : Nat) (hi : i<4) : (preparedCodeLimb (tr.cell 0 r) (502+16*i)).toNat=
      (amount/65536^i)%65536 := by
    have h:=fields (10+i) (by omega)
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3:=by omega
    rcases cases with z|z|z|z <;> subst i
    all_goals change (preparedCodeBits _).eval tr 0 r pub=Fp.ofNat _ at h
    all_goals rw [prepared_code_bits_eval] at h
    all_goals simp only [Bool.false_eq_true,ite_false] at h
    all_goals rw [h];exact prepared_code_digit_nat amount _
  have eq : preparedExecWord64 (tr.cell 0 r) 502=amount := by
    simp only [preparedExecWord64,preparedGasWord]
    rw [limbs 0 (by decide),limbs 1 (by decide),limbs 2 (by decide),limbs 3 (by decide)]
    exact prepared_code_digits64 amount bound
  exact ⟨live,by rw [eq];exact charge,by rw [eq];exact bound⟩

end NearCompression
