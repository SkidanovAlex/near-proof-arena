import NearCompression.PreparedTypedControlState
import NearCompression.PreparedTypedEqzAuthenticated
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
theorem prepared_typed_setup_block_state (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0) (block : tr.cell 0 r 605=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedTypedState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ e s',eligible.func.endOf[f.pc]?=some e ∧
      step cfg eligible.setup.program s=.cont s' ∧
      PreparedTypedState (tr.cell 0 (r+1)) s'
        {f with pc:=f.pc+1,labels:=[{target:=e+1,arity:=0,height:=sp,isLoop:=false},root]} fs sp count root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  obtain ⟨setup,func,checked⟩:=prepared_typed_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨_,op,fee,amount,targetValue,code,_,_,_,targetBound,_,target,fields⟩:=prepared_typed_authenticated_fetch codeCount count tr pub holds eligible.func _ checked r (by omega)
  obtain ⟨_,charge,bound⟩:=prepared_typed_authenticated_fee codeCount count tr pub holds eligible.func _ checked r (by omega)
  have tag:=fields 25 (by decide)
  change tr.cell 0 r 605=(if 4=op.tag then 1 else 0) at tag
  rw [block] at tag
  have opEq : op=PreparedTypedInstruction.control .block := by
    cases op with
    | control old=>
      cases old with
      | block=>rfl
      | brIf=>exact False.elim ((by decide : (1:Fp)≠0) tag)
      | legacy old=>cases old <;> exact False.elim ((by decide : (1:Fp)≠0) tag)
    | «local» kind i=>cases kind <;> exact False.elim ((by decide : (1:Fp)≠0) tag)
    | constant64 v=>exact False.elim ((by decide : (1:Fp)≠0) tag)
    | add64=>exact False.elim ((by decide : (1:Fp)≠0) tag)
    | eqz64=>exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  obtain ⟨e,endOf,targetEq⟩:=target rfl
  have lo:=fields 27 (by decide)
  have hi:=fields 28 (by decide)
  change (preparedCodeBits 607).eval tr 0 r pub=Fp.ofNat ((targetValue/65536^0)%65536) at lo
  change (preparedCodeBits 623).eval tr 0 r pub=Fp.ofNat ((targetValue/65536^1)%65536) at hi
  rw [prepared_code_bits_eval] at lo hi
  simp only [Bool.false_eq_true,ite_false] at lo hi
  have targetRow : (preparedCodeLimb (tr.cell 0 r) 607).toNat+65536*(preparedCodeLimb (tr.cell 0 r) 623).toNat=e+1 := by
    rw [lo,hi,prepared_code_digit_nat,prepared_code_digit_nat]
    simp only [Nat.pow_zero,Nat.pow_one,Nat.div_one]
    rw [prepared_code_digits32 targetValue targetBound,targetEq]
  rw [←state.pc] at code charge endOf
  have run:=prepared_typed_block_state count tr 0 r pub (prepared_typed_exec_local codeCount count tr pub holds)
    nonlast active block cfg eligible.setup.program s f fs sp root state eligible.func
    (by rw [fn];exact func) code e _ endOf targetRow charge bound rfl enough
  obtain ⟨s',step,state',done,failed⟩:=run
  exact ⟨e,s',endOf,step,state',done,failed⟩

/-- Nested end with actual preparation and authenticated CODE provenance. -/
theorem prepared_typed_setup_nested_end_state (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (endOp : tr.cell 0 r 469=1) (nested : tr.cell 0 r 639=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedTypedState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ s',step cfg eligible.setup.program s=.cont s' ∧
      PreparedTypedState (tr.cell 0 (r+1)) s'
        {f with pc:=f.pc+1,labels:=[root]} fs sp count root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  obtain ⟨setup,func,checked⟩:=prepared_typed_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨_,op,fee,amount,targetValue,code,_,_,_,targetBound,_,target,fields⟩:=prepared_typed_authenticated_fetch codeCount count tr pub holds eligible.func _ checked r (by omega)
  obtain ⟨_,charge,bound⟩:=prepared_typed_authenticated_fee codeCount count tr pub holds eligible.func _ checked r (by omega)
  have tag:=fields 7 (by decide)
  change tr.cell 0 r 469=(if 3=op.tag then 1 else 0) at tag
  rw [endOp] at tag
  have opEq : op=PreparedTypedInstruction.control (.legacy .end_) := by
    cases op with
    | control old=>
      cases old with
      | block=>exact False.elim ((by decide : (1:Fp)≠0) tag)
      | brIf=>exact False.elim ((by decide : (1:Fp)≠0) tag)
      | legacy old=>cases old <;> first | rfl | exact False.elim ((by decide : (1:Fp)≠0) tag)
    | «local» kind i=>cases kind <;> exact False.elim ((by decide : (1:Fp)≠0) tag)
    | constant64 v=>exact False.elim ((by decide : (1:Fp)≠0) tag)
    | add64=>exact False.elim ((by decide : (1:Fp)≠0) tag)
    | eqz64=>exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  rw [←state.pc] at code charge
  exact prepared_typed_nested_end_state count tr 0 r pub (prepared_typed_exec_local codeCount count tr pub holds)
    nonlast active endOp nested cfg eligible.setup.program s f fs sp root state eligible.func
    (by rw [fn];exact func) code _ charge bound rfl enough

end NearCompression
