import NearCompression.PreparedControlState
import NearCompression.PreparedControlSetup

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

theorem prepared_control_exec_local (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr) :
    TableLocal preparedControlLiteralExecTable tr 0 pub := by
  have ht : 0<(preparedControlLiteralAir count).tables.length := by change 0<2;decide
  exact ⟨(holds.logBound 0 ht).1,(holds.logBound 0 ht).2,holds.constr 0 ht,holds.bits 0 ht⟩

/-- Decode the authenticated message into actual charge, opcode selectors and
32-bit block target. All digit reconstruction is natural, avoiding aliases. -/
theorem prepared_control_authenticated_decode (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedControlCodeCheck pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) :
    let row:=tr.cell 0 r
    let pc:=preparedCodeExecPC row
    pc<pf.code.size ∧ ∃ op,
      pf.code[pc]?=some op.instr ∧
      PreparedWasmCharge pf pc (preparedExecWord64 row 502) ∧ preparedExecWord64 row 502<u64Bound ∧
      (∀ i,i<6 → row (preparedControlOpcodeColumn i)=if i=op.tag then 1 else 0) ∧
      (op=PreparedControlInstruction.block → ∃ e,pf.endOf[pc]?=some e ∧
        (preparedCodeLimb row 607).toNat+65536*(preparedCodeLimb row 623).toNat=e+1) := by
  obtain ⟨live,op,fee,amount,target,code,gas,charge,bound,targetBound,targetEq,fields⟩:=
    prepared_control_authenticated_fetch count tr pub holds pf fn checked r hr
  have limbs (i : Nat) (hi : i<4) : (preparedCodeLimb (tr.cell 0 r) (502+16*i)).toNat=
      (amount/65536^i)%65536 := by
    have h:=fields (10+i) (by omega)
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3:=by omega
    rcases cases with z|z|z|z <;> subst i
    all_goals change (preparedCodeBits _).eval tr 0 r pub=Fp.ofNat _ at h
    all_goals rw [prepared_code_bits_eval] at h
    all_goals simp only [Bool.false_eq_true,ite_false] at h
    all_goals rw [h];exact prepared_code_digit_nat amount _
  have amountEq : preparedExecWord64 (tr.cell 0 r) 502=amount := by
    simp only [preparedExecWord64,preparedGasWord]
    rw [limbs 0 (by decide),limbs 1 (by decide),limbs 2 (by decide),limbs 3 (by decide)]
    exact prepared_code_digits64 amount bound
  refine ⟨live,op,code,by rw [amountEq];exact charge,by rw [amountEq];exact bound,?_,?_⟩
  · intro i hi
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5:=by omega
    rcases cases with z|z|z|z|z|z <;> subst i
    · exact fields 4 (by decide)
    · exact fields 5 (by decide)
    · exact fields 6 (by decide)
    · exact fields 7 (by decide)
    · exact fields 25 (by decide)
    · exact fields 26 (by decide)
  · intro block
    obtain ⟨e,actual,eq⟩:=targetEq block
    have low:=fields 27 (by decide)
    have high:=fields 28 (by decide)
    change (preparedCodeBits 607).eval tr 0 r pub=Fp.ofNat ((target/65536^0)%65536) at low
    change (preparedCodeBits 623).eval tr 0 r pub=Fp.ofNat ((target/65536^1)%65536) at high
    simp only [Nat.reducePow,Nat.div_one] at low high
    rw [prepared_code_bits_eval] at low high
    simp only [Bool.false_eq_true,ite_false] at low high
    refine ⟨e,actual,?_⟩
    rw [low,high]
    have l:=prepared_code_digit_nat target 0
    have h:=prepared_code_digit_nat target 1
    simp only [Nat.reducePow,Nat.div_one] at l h
    rw [l,h,prepared_code_digits32 target targetBound,eq]

/-- Source bytes determine the actual prepared function. Frame.fn is tied to
that same function; no arbitrary PFunc or caller-supplied fee/target remains. -/
theorem prepared_control_setup_block_state (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedControlSetupCheck cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0) (block : tr.cell 0 r 605=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedControlState (tr.cell 0 r) s f fs sp root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ e s',eligible.func.endOf[f.pc]?=some e ∧
      step cfg eligible.setup.program s=.cont s' ∧
      PreparedControlState (tr.cell 0 (r+1)) s'
        {f with pc:=f.pc+1,labels:=[{target:=e+1,arity:=0,height:=sp,isLoop:=false},root]} fs sp root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  obtain ⟨setup,func,checked⟩:=prepared_control_setup_checked cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨_,op,code,charge,bound,ops,target⟩:=prepared_control_authenticated_decode count tr pub holds eligible.func _ checked r (by omega)
  have tag:=ops 4 (by decide)
  change tr.cell 0 r 605=(if 4=op.tag then 1 else 0) at tag
  rw [block] at tag
  have opEq : op=PreparedControlInstruction.block := by
    cases op with
    | block => rfl
    | brIf => exact False.elim ((by decide : (1:Fp)≠0) tag)
    | legacy old => cases old <;> exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  obtain ⟨e,endOf,targetEq⟩:=target rfl
  rw [←state.1.pc] at code charge endOf
  have run:=prepared_control_block_state tr 0 r pub (prepared_control_exec_local count tr pub holds)
    nonlast active block cfg eligible.setup.program s f fs sp root state eligible.func
    (by rw [fn];exact func) code e _ endOf targetEq charge bound rfl enough
  obtain ⟨s',step,state',done,failed⟩:=run
  exact ⟨e,s',endOf,step,state',done,failed⟩

/-- Nested end with actual preparation and authenticated CODE provenance. -/
theorem prepared_control_setup_nested_end_state (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedControlSetupCheck cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (endOp : tr.cell 0 r 469=1) (nested : tr.cell 0 r 639=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedControlState (tr.cell 0 r) s f fs sp root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ s',step cfg eligible.setup.program s=.cont s' ∧
      PreparedControlState (tr.cell 0 (r+1)) s'
        {f with pc:=f.pc+1,labels:=[root]} fs sp root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  obtain ⟨setup,func,checked⟩:=prepared_control_setup_checked cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨_,op,code,charge,bound,ops,_⟩:=prepared_control_authenticated_decode count tr pub holds eligible.func _ checked r (by omega)
  have tag:=ops 3 (by decide)
  change tr.cell 0 r 469=(if 3=op.tag then 1 else 0) at tag
  rw [endOp] at tag
  have opEq : op=PreparedControlInstruction.legacy .end_ := by
    cases op with
    | block => exact False.elim ((by decide : (1:Fp)≠0) tag)
    | brIf => exact False.elim ((by decide : (1:Fp)≠0) tag)
    | legacy old => cases old <;> first | rfl | exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  rw [←state.1.pc] at code charge
  exact prepared_control_nested_end_state tr 0 r pub (prepared_control_exec_local count tr pub holds)
    nonlast active endOp nested cfg eligible.setup.program s f fs sp root state eligible.func
    (by rw [fn];exact func) code _ charge bound rfl enough

end NearCompression
