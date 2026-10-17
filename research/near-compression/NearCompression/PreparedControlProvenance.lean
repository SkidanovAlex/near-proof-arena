import NearCompression.PreparedControlBus
import NearCompression.PreparedControlStep

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.Wasm

theorem prepared_control_public_record_field (pub : List Fp) (pc field : Nat) (hf : field<29) :
    (preparedControlBusPublicSegment.record pub pc).getD field 0=pub.getD (66+29*pc+field) 0 := by
  simp only [PubSeg.record,preparedControlBusPublicSegment,List.map_nil,List.nil_append,PubSeg.startOffset,
    List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hf,Option.map_some,Option.getD_some]
  rw [Nat.mul_comm pc 29]

theorem prepared_control_record_pc (pf : PFunc) (fn : Nat) (pub : List Fp)
    (accepted : preparedControlCodeCheck pf fn pub=true) (pc : Nat) (live : pc<pf.code.size) :
    ((preparedControlBusPublicSegment.record pub pc).getD 2 0).toNat+
      65536*((preparedControlBusPublicSegment.record pub pc).getD 3 0).toNat=pc := by
  obtain ⟨op,fee,amount,target,_,_,_,_,_,_,fields⟩:=prepared_control_code_checked pf fn pub accepted pc live
  rw [prepared_control_public_record_field pub pc 2 (by decide),prepared_control_public_record_field pub pc 3 (by decide),
    fields 2 (by decide),fields 3 (by decide)]
  simp only [preparedControlField,Nat.reduceLT,ite_false,ite_true,Nat.reduceSub,
    Nat.reducePow,Nat.div_one]
  have shape:=accepted
  simp only [preparedControlCodeCheck,Bool.and_eq_true,decide_eq_true_eq] at shape
  have d0:=prepared_code_digit_nat pc 0
  have d1:=prepared_code_digit_nat pc 1
  simp only [Nat.reducePow,Nat.div_one] at d0 d1
  rw [d0,d1]
  exact prepared_code_digits32 pc (by omega)

/-- Literal fetch plus the executable prepared-code checker supplies the
actual instruction, charge and authenticated endOf target at the actual PC.
There is no supplied live-PC, operand, target, or fetch-equation premise. -/
theorem prepared_control_authenticated_fetch (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedControlCodeCheck pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) :
    let pc:=preparedCodeExecPC (tr.cell 0 r)
    pc<pf.code.size ∧ ∃ op fee amount target,
      pf.code[pc]?=some op.instr ∧ pf.gas[pc]?=some fee ∧
      PreparedWasmCharge pf pc amount ∧ amount<u64Bound ∧ target<4294967296 ∧
      (op=PreparedControlInstruction.block → ∃ e,pf.endOf[pc]?=some e ∧ target=e+1) ∧
      ∀ field,field<29 → (preparedControlBusFetch.msgVal tr 0 r pub).getD field 0=
        preparedControlField fn pc op fee amount target field := by
  obtain ⟨_,_,_,j,hj,published⟩:=prepared_control_literal_fetch count tr pub holds r hr
  have shape:=checked
  simp only [preparedControlCodeCheck,Bool.and_eq_true,decide_eq_true_eq] at shape
  have live : j<pf.code.size := by
    change j<preparedCodePublicSegment.count pub at hj
    rw [shape.1.2.2.2.2.2] at hj
    exact hj
  have canonical:=prepared_control_record_pc pf fn pub checked j live
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
  obtain ⟨op,fee,amount,target,code,gas,charge,bound,targetBound,targetEq,fields⟩:=
    prepared_control_code_checked pf fn pub checked _ live
  refine ⟨op,fee,amount,target,code,gas,charge,bound,targetBound,targetEq,?_⟩
  intro field hf
  rw [←published,prepared_control_public_record_field pub _ field hf,fields field hf]

end NearCompression
