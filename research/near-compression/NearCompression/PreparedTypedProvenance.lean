import NearCompression.PreparedTypedBus
import NearCompression.PreparedTypedCode
import NearCompression.PreparedControlGas

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.Wasm

theorem prepared_typed_public_record_field (pub : List Fp) (pc field : Nat) (hf : field<37) :
    (preparedTypedBusPublicSegment.record pub pc).getD field 0=pub.getD (118+37*pc+field) 0 := by
  simp only [PubSeg.record,preparedTypedBusPublicSegment,List.map_nil,List.nil_append,PubSeg.startOffset,
    List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hf,Option.map_some,Option.getD_some]
  rw [Nat.mul_comm pc 37]

theorem prepared_typed_record_pc (count : Nat) (pf : PFunc) (fn : Nat) (pub : List Fp)
    (accepted : preparedTypedCodeCheck count pf fn pub=true) (pc : Nat) (live : pc<pf.code.size) :
    ((preparedTypedBusPublicSegment.record pub pc).getD 2 0).toNat+
      65536*((preparedTypedBusPublicSegment.record pub pc).getD 3 0).toNat=pc := by
  obtain ⟨op,fee,amount,target,_,_,_,_,_,_,fields⟩:=prepared_typed_entry_checked pf fn pub pc
    (prepared_typed_code_entry count pf fn pub accepted pc live)
  rw [prepared_typed_public_record_field pub pc 2 (by decide),prepared_typed_public_record_field pub pc 3 (by decide),
    fields 2 (by decide),fields 3 (by decide)]
  simp only [preparedTypedField,Nat.reduceLT,ite_false,ite_true,Nat.reduceSub,
    Nat.reducePow,Nat.div_one]
  obtain ⟨_,_,_,_,_,_,_,bound,_,_,_,_⟩:=prepared_typed_code_shape count pf fn pub accepted
  have d0:=prepared_code_digit_nat pc 0
  have d1:=prepared_code_digit_nat pc 1
  simp only [Nat.reducePow,Nat.div_one] at d0 d1
  rw [d0,d1]
  exact prepared_code_digits32 pc (by omega)

/-- Literal fetch and actual prepared-code validation identify the interpreter
instruction and charge at the execution row's PC, including local index bounds.
No supplied live-PC, fetch equation or CODE uniqueness premise remains. -/
theorem prepared_typed_authenticated_fetch (codeCount localCount : Nat)
    (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount localCount) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedTypedCodeCheck localCount pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) :
    let pc:=preparedCodeExecPC (tr.cell 0 r)
    pc<pf.code.size ∧ ∃ op fee amount target,
      pf.code[pc]?=some op.instr ∧ pf.gas[pc]?=some fee ∧
      PreparedWasmCharge pf pc amount ∧ amount<u64Bound ∧ target<4294967296 ∧
      (∀ kind index,op=PreparedTypedInstruction.local kind index → index<pf.locals.size) ∧
      (op=PreparedTypedInstruction.control .block → ∃ e,pf.endOf[pc]?=some e ∧ target=e+1) ∧
      ∀ field,field<37 → (preparedTypedBusFetch.msgVal tr 0 r pub).getD field 0=
        preparedTypedField fn pc op fee amount target field := by
  obtain ⟨_,_,_,j,hj,published⟩:=prepared_typed_literal_fetch codeCount localCount tr pub holds r hr
  obtain ⟨_,_,_,_,_,_,_,_,_,_,countEq,_⟩:=prepared_typed_code_shape localCount pf fn pub checked
  have live : j<pf.code.size := by
    change j<preparedCodePublicSegment.count pub at hj
    rw [countEq] at hj
    exact hj
  have canonical:=prepared_typed_record_pc localCount pf fn pub checked j live
  have lo:=congrArg (fun xs:List Fp=>xs.getD 2 0) published
  have hi:=congrArg (fun xs:List Fp=>xs.getD 3 0) published
  change _=(preparedCodeBits 0).eval tr 0 r pub at lo
  change _=(preparedCodeBits 16).eval tr 0 r pub at hi
  rw [prepared_code_bits_eval] at lo hi
  have index : j=preparedCodeExecPC (tr.cell 0 r) := by
    rw [lo,hi] at canonical
    exact canonical.symm
  subst j
  refine ⟨live,?_⟩
  obtain ⟨op,fee,amount,target,code,gas,charge,bound,indices,targetEq,fields⟩:=
    prepared_typed_entry_checked pf fn pub _
      (prepared_typed_code_entry localCount pf fn pub checked _ live)
  have targetChecked:=prepared_typed_target_checked pf _ op target targetEq
  refine ⟨op,fee,amount,target,code,gas,charge,bound,targetChecked.1,indices,targetChecked.2,?_⟩
  intro field hf
  rw [←published,prepared_typed_public_record_field pub _ field hf,fields field hf]

/-- Authenticated37-field descriptor reconstructs the actual prepared fee.
No independent fee equality or fee bound is supplied. -/
theorem prepared_typed_authenticated_fee (codeCount localCount : Nat)
    (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount localCount) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedTypedCodeCheck localCount pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) :
    let pc:=preparedCodeExecPC (tr.cell 0 r)
    pc<pf.code.size ∧ PreparedWasmCharge pf pc (preparedExecWord64 (tr.cell 0 r) 502) ∧
      preparedExecWord64 (tr.cell 0 r) 502<u64Bound := by
  obtain ⟨live,op,fee,amount,target,code,gas,charge,bound,_,_,_,fields⟩:=
    prepared_typed_authenticated_fetch codeCount localCount tr pub holds pf fn checked r hr
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
theorem prepared_typed_setup_authenticated_fee (codeCount localCount : Nat)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel : Bool) (eligible : PreparedRunCallEligible)
    (tr : Trace Fp) (pub : List Fp)
    (accepted : preparedTypedSetupCheck localCount cfg bytes method ctx pub blockLevel=some eligible)
    (holds : HoldsP (preparedTypedLiteralAir codeCount localCount) pub tr)
    (r : Nat) (hr : r<tr.height 0) :
    let pc:=preparedCodeExecPC (tr.cell 0 r)
    pc<eligible.func.code.size ∧ PreparedWasmCharge eligible.func pc (preparedExecWord64 (tr.cell 0 r) 502) ∧
      preparedExecWord64 (tr.cell 0 r) 502<u64Bound := by
  have setup:=prepared_typed_setup_checked localCount cfg bytes method ctx pub blockLevel eligible accepted
  exact prepared_typed_authenticated_fee codeCount localCount tr pub holds eligible.func
    (eligible.setup.methodIndex-eligible.setup.program.m.imports.size) setup.2.2 r hr

end NearCompression
