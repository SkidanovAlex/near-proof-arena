import NearCompression.PreparedLocalsBus
import NearCompression.PreparedLocalsCode

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.Wasm

theorem prepared_locals_public_record_field (pub : List Fp) (pc field : Nat) (hf : field<32) :
    (preparedLocalsBusPublicSegment.record pub pc).getD field 0=pub.getD (66+32*pc+field) 0 := by
  simp only [PubSeg.record,preparedLocalsBusPublicSegment,List.map_nil,List.nil_append,PubSeg.startOffset,
    List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hf,Option.map_some,Option.getD_some]
  rw [Nat.mul_comm pc 32]

theorem prepared_locals_record_pc (count : Nat) (pf : PFunc) (fn : Nat) (pub : List Fp)
    (accepted : preparedLocalsCodeCheck count pf fn pub=true) (pc : Nat) (live : pc<pf.code.size) :
    ((preparedLocalsBusPublicSegment.record pub pc).getD 2 0).toNat+
      65536*((preparedLocalsBusPublicSegment.record pub pc).getD 3 0).toNat=pc := by
  obtain ⟨op,fee,amount,target,_,_,_,_,_,_,fields⟩:=prepared_locals_entry_checked pf fn pub pc
    (prepared_locals_code_entry count pf fn pub accepted pc live)
  rw [prepared_locals_public_record_field pub pc 2 (by decide),prepared_locals_public_record_field pub pc 3 (by decide),
    fields 2 (by decide),fields 3 (by decide)]
  simp only [preparedLocalsField,Nat.reduceLT,ite_false,ite_true,Nat.reduceSub,
    Nat.reducePow,Nat.div_one]
  obtain ⟨_,_,_,_,_,_,_,bound,_,_,_⟩:=prepared_locals_code_shape count pf fn pub accepted
  have d0:=prepared_code_digit_nat pc 0
  have d1:=prepared_code_digit_nat pc 1
  simp only [Nat.reducePow,Nat.div_one] at d0 d1
  rw [d0,d1]
  exact prepared_code_digits32 pc (by omega)

/-- Literal fetch and actual prepared-code validation identify the interpreter
instruction and charge at the execution row's PC, including local index bounds.
No supplied live-PC, fetch equation or CODE uniqueness premise remains. -/
theorem prepared_locals_authenticated_fetch (codeCount localCount : Nat)
    (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount localCount) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedLocalsCodeCheck localCount pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) :
    let pc:=preparedCodeExecPC (tr.cell 0 r)
    pc<pf.code.size ∧ ∃ op fee amount target,
      pf.code[pc]?=some op.instr ∧ pf.gas[pc]?=some fee ∧
      PreparedWasmCharge pf pc amount ∧ amount<u64Bound ∧ target<4294967296 ∧
      (∀ kind index,op=PreparedLocalsInstruction.local kind index → index<pf.locals.size) ∧
      (op=PreparedLocalsInstruction.control .block → ∃ e,pf.endOf[pc]?=some e ∧ target=e+1) ∧
      ∀ field,field<32 → (preparedLocalsBusFetch.msgVal tr 0 r pub).getD field 0=
        preparedLocalsField fn pc op fee amount target field := by
  obtain ⟨_,_,_,j,hj,published⟩:=prepared_locals_literal_fetch codeCount localCount tr pub holds r hr
  obtain ⟨_,_,_,_,_,_,_,_,_,_,countEq⟩:=prepared_locals_code_shape localCount pf fn pub checked
  have live : j<pf.code.size := by
    change j<preparedCodePublicSegment.count pub at hj
    rw [countEq] at hj
    exact hj
  have canonical:=prepared_locals_record_pc localCount pf fn pub checked j live
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
    prepared_locals_entry_checked pf fn pub _
      (prepared_locals_code_entry localCount pf fn pub checked _ live)
  have targetChecked:=prepared_locals_target_checked pf _ op target targetEq
  refine ⟨op,fee,amount,target,code,gas,charge,bound,targetChecked.1,indices,targetChecked.2,?_⟩
  intro field hf
  rw [←published,prepared_locals_public_record_field pub _ field hf,fields field hf]

end NearCompression
