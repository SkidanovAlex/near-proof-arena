import NearCompression.PreparedLocalsIndex
import NearCompression.PreparedControlGas
import NearCompression.PreparedLocalsProvenance
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
private theorem locals_gas_boolean_prefix :
    preparedLocalsLiteralExecBase.take 682=(List.range 682).map preparedGasBoolean := by rfl
private theorem locals_gas_subtract_at : ∀ i:Fin 4,
    preparedLocalsLiteralExecBase[998+i.val]'(by change _<1144;omega)=preparedExecGasSubtract i.val := by decide
private theorem locals_gas_update_at : ∀ i:Fin 4,
    preparedLocalsLiteralExecBase[1106+i.val]'(by change _<1144;omega)=preparedExecGasUpdate i.val := by decide
/-- Reuses proved gas borrowing/update semantics from exact locals AIR sources. -/
theorem prepared_locals_gas_source (count : Nat) :
    PreparedControlGasSource (preparedLocalsLiteralExecTable count) := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    apply prepared_locals_base_member
    apply List.mem_of_mem_take
    rw [locals_gas_boolean_prefix]
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  · intro i hi
    apply prepared_locals_base_member
    have h:=List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=998+i) (by change _<1144;omega)
    rw [locals_gas_subtract_at ⟨i,hi⟩] at h
    exact h
  · intro i hi
    apply prepared_locals_base_member
    have h:=List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=1106+i) (by change _<1144;omega)
    rw [locals_gas_update_at ⟨i,hi⟩] at h
    exact h

/-- Authenticated32field descriptor reconstructs the actual prepared fee.
No independent fee equality or fee bound is supplied. -/
theorem prepared_locals_authenticated_fee (codeCount localCount : Nat)
    (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount localCount) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedLocalsCodeCheck localCount pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) :
    let pc:=preparedCodeExecPC (tr.cell 0 r)
    pc<pf.code.size ∧ PreparedWasmCharge pf pc (preparedExecWord64 (tr.cell 0 r) 502) ∧
      preparedExecWord64 (tr.cell 0 r) 502<u64Bound := by
  obtain ⟨live,op,fee,amount,target,code,gas,charge,bound,_,_,_,fields⟩:=
    prepared_locals_authenticated_fetch codeCount localCount tr pub holds pf fn checked r hr
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

/-- The same fee result for an actual prepare/link/load/resolve result;
the function is obtained from setup, not supplied independently. -/
theorem prepared_locals_setup_authenticated_fee (codeCount localCount : Nat)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel : Bool) (eligible : PreparedRunCallEligible)
    (tr : Trace Fp) (pub : List Fp)
    (accepted : preparedLocalsSetupCheck localCount cfg bytes method ctx pub blockLevel=some eligible)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount localCount) pub tr)
    (r : Nat) (hr : r<tr.height 0) :
    let pc:=preparedCodeExecPC (tr.cell 0 r)
    pc<eligible.func.code.size ∧ PreparedWasmCharge eligible.func pc (preparedExecWord64 (tr.cell 0 r) 502) ∧
      preparedExecWord64 (tr.cell 0 r) 502<u64Bound := by
  have setup:=prepared_locals_setup_checked localCount cfg bytes method ctx pub blockLevel eligible accepted
  exact prepared_locals_authenticated_fee codeCount localCount tr pub holds eligible.func
    (eligible.setup.methodIndex-eligible.setup.program.m.imports.size) setup.2.2 r hr

end NearCompression
