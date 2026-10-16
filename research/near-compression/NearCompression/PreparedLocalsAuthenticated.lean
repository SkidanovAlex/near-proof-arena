import NearCompression.PreparedLocalsGas
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 200000

def preparedLocalsKindTag : PreparedLocalOp → Nat
  | .get=>6 | .set=>7 | .tee=>8

theorem prepared_locals_exec_local (codeCount localCount : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount localCount) pub tr) :
    TableLocal (preparedLocalsLiteralExecTable localCount) tr 0 pub := by
  have ht : 0<(preparedLocalsLiteralAir codeCount localCount).tables.length := by change 0<2;decide
  exact ⟨(holds.logBound 0 ht).1,(holds.logBound 0 ht).2,holds.constr 0 ht,holds.bits 0 ht⟩

/-- Actual authenticated local instruction and canonical immediate, without a
caller-supplied CODE record or immediate lookup. -/
theorem prepared_locals_authenticated_instruction (codeCount localCount : Nat)
    (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount localCount) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedLocalsCodeCheck localCount pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) (kind : PreparedLocalOp)
    (tag : tr.cell 0 r (677+preparedLocalsKindTag kind)=1) :
    ∃ index, index<localCount ∧
      pf.code[preparedCodeExecPC (tr.cell 0 r)]?=some (kind.instr index) ∧
      (preparedCodeLimb (tr.cell 0 r) 470).toNat+
        65536*(preparedCodeLimb (tr.cell 0 r) 486).toNat=index ∧
      tr.cell 0 r 683+(tr.cell 0 r 684+tr.cell 0 r 685)=1 := by
  obtain ⟨live,op,fee,amount,target,code,gas,charge,bound,tbound,valid,targetEq,fields⟩:=
    prepared_locals_authenticated_fetch codeCount localCount tr pub holds pf fn checked r hr
  have tags : tr.cell 0 r (677+preparedLocalsKindTag kind)=
      (if preparedLocalsKindTag kind=op.tag then 1 else 0) := by
    cases kind
    · exact fields 29 (by decide)
    · exact fields 30 (by decide)
    · exact fields 31 (by decide)
  have eq : ∃ index,op=.local kind index := by
    rw [tag] at tags
    cases op with
    | control old =>
      cases kind <;> cases old with
      | legacy old => cases old <;> exact False.elim ((by decide : (1:Fp)≠0) tags)
      | block => exact False.elim ((by decide : (1:Fp)≠0) tags)
      | brIf => exact False.elim ((by decide : (1:Fp)≠0) tags)
    | «local» k index =>
      cases kind <;> cases k <;> first
        | exact ⟨index,rfl⟩
        | exact False.elim ((by decide : (1:Fp)≠0) tags)
  obtain ⟨index,rfl⟩:=eq
  have shape:=prepared_locals_code_shape localCount pf fn pub checked
  have indexBound:=valid kind index rfl
  have hc : index<localCount := by omega
  have low:=fields 8 (by decide)
  have high:=fields 9 (by decide)
  change (preparedCodeBits 470).eval tr 0 r pub=Fp.ofNat ((index/65536^0)%65536) at low
  change (preparedCodeBits 486).eval tr 0 r pub=Fp.ofNat ((index/65536^1)%65536) at high
  rw [prepared_code_bits_eval] at low high
  simp only [Bool.false_eq_true,ite_false] at low high
  refine ⟨index,hc,code,?_,?_⟩
  · rw [low,high,prepared_code_digit_nat index 0,prepared_code_digit_nat index 1]
    simpa only [Nat.reducePow,Nat.div_one] using prepared_code_digits32 index (by omega)
  · have g:=fields 29 (by decide)
    have s:=fields 30 (by decide)
    have t:=fields 31 (by decide)
    change tr.cell 0 r 683=(if 6=(PreparedLocalsInstruction.local kind index).tag then 1 else 0) at g
    change tr.cell 0 r 684=(if 7=(PreparedLocalsInstruction.local kind index).tag then 1 else 0) at s
    change tr.cell 0 r 685=(if 8=(PreparedLocalsInstruction.local kind index).tag then 1 else 0) at t
    rw [g,s,t]
    cases kind <;> simp only [PreparedLocalsInstruction.tag, Nat.reduceEqDiff, ite_true, ite_false] <;> grind


/-- The one-hot local selector selects the actual authenticated immediate. -/
theorem prepared_locals_authenticated_selected (codeCount localCount : Nat)
    (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount localCount) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedLocalsCodeCheck localCount pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) (kind : PreparedLocalOp)
    (tag : tr.cell 0 r (677+preparedLocalsKindTag kind)=1) :
    ∃ index, index<localCount ∧
      pf.code[preparedCodeExecPC (tr.cell 0 r)]?=some (kind.instr index) ∧
      ∀j,j<4 → tr.cell 0 r (814+j)=if j=index then 1 else 0 := by
  obtain ⟨index,valid,code,imm,ops⟩:=prepared_locals_authenticated_instruction
    codeCount localCount tr pub holds pf fn checked r hr kind tag
  have localH:=prepared_locals_exec_local codeCount localCount tr pub holds
  have shape:=prepared_locals_code_shape localCount pf fn pub checked
  obtain ⟨selected,bound,hot⟩:=prepared_locals_selected localCount shape.2.1 tr 0 r pub localH hr ops
  have eq:=prepared_locals_index localCount tr 0 r pub localH hr ops selected (Nat.lt_of_lt_of_le bound shape.2.1) hot
  have same : selected=index := eq.symm.trans imm
  exact ⟨index,valid,code,same ▸ hot⟩
end NearCompression
