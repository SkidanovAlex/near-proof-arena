import NearCompression.PreparedLocalsAuthenticated
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536

/-- Decode any of the six inherited opcode tags through the new 32-field
CODE bus. Local tags are proven zero; immediates and block targets are exact
natural integers rather than field aliases. -/
theorem prepared_locals_control_decode (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedLocalsCodeCheck count pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) (tag : Nat) (tagBound : tag<6)
    (selected : tr.cell 0 r (preparedControlOpcodeColumn tag)=1) :
    ∃ op:PreparedControlInstruction,
      pf.code[preparedCodeExecPC (tr.cell 0 r)]?=some op.instr ∧
      PreparedWasmCharge pf (preparedCodeExecPC (tr.cell 0 r)) (preparedExecWord64 (tr.cell 0 r) 502) ∧
      preparedExecWord64 (tr.cell 0 r) 502<u64Bound ∧
      preparedExecImmediate (tr.cell 0 r)=op.immediate ∧
      (∀i,i<6 → tr.cell 0 r (preparedControlOpcodeColumn i)=if i=op.tag then 1 else 0) ∧
      (∀i,i<3 → tr.cell 0 r (683+i)=0) ∧
      (op=.block → ∃e,pf.endOf[preparedCodeExecPC (tr.cell 0 r)]?=some e ∧
        (preparedCodeLimb (tr.cell 0 r) 607).toNat+65536*(preparedCodeLimb (tr.cell 0 r) 623).toNat=e+1) := by
  obtain ⟨_,op,fee,amount,target,code,gas,charge,bound,targetBound,localBound,targetEq,fields⟩:=
    prepared_locals_authenticated_fetch codeCount count tr pub holds pf fn checked r hr
  have ops : ∀i,i<6 → tr.cell 0 r (preparedControlOpcodeColumn i)=if i=op.tag then 1 else 0 := by
    intro i hi
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5:=by omega
    rcases cases with z|z|z|z|z|z <;> subst i
    · exact fields 4 (by decide)
    · exact fields 5 (by decide)
    · exact fields 6 (by decide)
    · exact fields 7 (by decide)
    · exact fields 25 (by decide)
    · exact fields 26 (by decide)
  have isControl : ∃old,op=.control old := by
    cases op with
    | control old => exact ⟨old,rfl⟩
    | «local» kind index =>
      have h:=ops tag tagBound
      rw [selected] at h
      have ne : ¬tag=(PreparedLocalsInstruction.local kind index).tag := by
        cases kind <;> simp only [PreparedLocalsInstruction.tag] <;> omega
      rw [ite_eq_right ne] at h
      exact False.elim ((by decide : (1:Fp)≠0) h)
  obtain ⟨old,eq⟩:=isControl
  have code':=eq ▸ code
  have fields':=eq ▸ fields
  have ops':=eq ▸ ops
  have targetEq':=eq ▸ targetEq
  obtain ⟨_,realCharge,realBound⟩:=prepared_locals_authenticated_fee codeCount count tr pub holds pf fn checked r hr
  refine ⟨old,code',realCharge,realBound,?_,ops',?_,?_⟩
  · have lo:=fields' 8 (by decide)
    have hi:=fields' 9 (by decide)
    change (preparedCodeBits 470).eval tr 0 r pub=Fp.ofNat ((old.immediate/65536^0)%65536) at lo
    change (preparedCodeBits 486).eval tr 0 r pub=Fp.ofNat ((old.immediate/65536^1)%65536) at hi
    rw [prepared_code_bits_eval] at lo hi
    simp only [Bool.false_eq_true,ite_false] at lo hi
    unfold preparedExecImmediate
    rw [lo,hi,prepared_code_digit_nat,prepared_code_digit_nat]
    simp only [Nat.reducePow,Nat.div_one]
    apply prepared_code_digits32
    cases old with
    | legacy legacy => cases legacy with
      | constant v => exact v.toNat_lt
      | _ => decide
    | _ => decide
  · intro i hi
    have h:=fields' (29+i) (by omega)
    have cases : i=0 ∨ i=1 ∨ i=2:=by omega
    rcases cases with z|z|z <;> subst i
    all_goals cases old with
      | legacy legacy => cases legacy <;> exact h
      | block | brIf => exact h
  · intro block
    obtain ⟨e,actual,eq⟩:=targetEq' (by rw [block])
    have low:=fields' 27 (by decide)
    have high:=fields' 28 (by decide)
    change (preparedCodeBits 607).eval tr 0 r pub=Fp.ofNat ((target/65536^0)%65536) at low
    change (preparedCodeBits 623).eval tr 0 r pub=Fp.ofNat ((target/65536^1)%65536) at high
    rw [prepared_code_bits_eval] at low high
    simp only [Bool.false_eq_true,ite_false] at low high
    refine ⟨e,actual,?_⟩
    rw [low,high,prepared_code_digit_nat,prepared_code_digit_nat]
    simp only [Nat.reducePow,Nat.div_one]
    rw [prepared_code_digits32 target targetBound,eq]
end NearCompression
