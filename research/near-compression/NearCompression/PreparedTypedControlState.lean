import NearCompression.PreparedTypedBlock
import NearCompression.PreparedTypedFrameDepth
import NearCompression.PreparedTypedEqzState
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
theorem prepared_typed_block_state (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (block : tr.cell t r 605=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (sp : Nat) (root : Label) (state : PreparedTypedState (tr.cell t r) s f fs sp count root)
    (pf : PFunc) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some (.block none)) (e amount : Nat)
    (target : pf.endOf[f.pc]?=some e)
    (targetRow : (preparedCodeLimb (tr.cell t r) 607).toNat+65536*(preparedCodeLimb (tr.cell t r) 623).toNat=e+1)
    (charge : PreparedWasmCharge pf f.pc amount) (bounded : amount<u64Bound)
    (fee : preparedExecWord64 (tr.cell t r) 502=amount) (enough : amount≤s.gas.g) :
    ∃ s',step cfg p s=.cont s' ∧
      PreparedTypedState (tr.cell t (r+1)) s'
        {f with pc:=f.pc+1,labels:=[{target:=e+1,arity:=0,height:=sp,isLoop:=false},root]} fs sp count root ∧
      tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have flags:=prepared_typed_opcode_selected count state.countBound tr t r pub localH (by omega) 4 (by decide) block
  have set0:=flags 7 (by decide);have tee0:=flags 8 (by decide)
  change tr.cell t r 684=0 at set0
  change tr.cell t r 685=0 at tee0
  have preserve:=prepared_typed_local_array_preserve count state.countBound tr t r pub localH nonlast set0 tee0
  have localsEq : f.locals=preparedTypedLocalArray (tr.cell t (r+1)) count:=state.locals.trans preserve.symm
  have enoughRow : preparedExecWord64 (tr.cell t r) 502≤preparedExecWord64 (tr.cell t r) 299 := by
    rw [fee,←state.gas];exact enough
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr t r pub (prepared_typed_gas_source count state.countBound) localH nonlast active enoughRow
  have projection:=prepared_typed_block_label count state.countBound tr t r pub localH nonlast active charged block
  have labels : f.labels=[root] := by
    rcases state.labels with h|⟨height,_,present,_,_⟩
    · exact h.2
    · rw [projection.1] at present
      exact False.elim ((by decide : (0:Fp)≠1) present)
  have nextSelected:=prepared_typed_frame_depth count state.countBound tr t r pub localH nonlast 4 (Or.inr rfl) block sp state.depth state.selected
  have stack : preparedTypedStack (tr.cell t (r+1)) sp=s.stack := by
    rw [state.stack]
    apply prepared_typed_stack_congr
    intro i hi
    exact prepared_typed_frame_stack_value count state.countBound tr t r pub localH nonlast 4 (Or.inr rfl) block i (by have hs:=state.depth;omega)
  have size : s.stack.size=sp := by simp [state.stack,preparedTypedStack]
  have saved : preparedControlSavedTarget (tr.cell t (r+1))=e+1 := by
    have l:=projection.2.2.2.1 0 (by decide)
    have h:=projection.2.2.2.1 1 (by decide)
    simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one,Nat.reduceAdd] at l h
    unfold preparedControlSavedTarget
    rw [l,h];exact targetRow
  have run:=prepared_control_step_block cfg p s f fs pf amount e state.frames func code target charge bounded enough
  rw [size,labels] at run
  let f' : Frame:={f with pc:=f.pc+1,labels:=[{target:=e+1,arity:=0,height:=sp,isLoop:=false},root]}
  let s' : St:={s with frames:=f'::fs,gas:={s.gas with g:=s.gas.g-amount}}
  have run' : step cfg p s=.cont s' := by
    simpa only [setFrame,state.frames] using run
  refine ⟨s',run',?_,projection.2.2.2.2.2.1,projection.2.2.2.2.2.2⟩
  · refine ⟨state.depth,nextSelected,rfl,?_,stack.symm,?_,state.countBound,localsEq,?_⟩
    · change f.pc+1=preparedCodeExecPC (tr.cell t (r+1))
      rw [state.pc,projection.2.2.2.2.1]
    · change s.gas.g-amount=preparedExecWord64 (tr.cell t (r+1)) 299
      rw [gas,fee,state.gas]
    · right
      refine ⟨sp,state.depth,projection.2.1,?_,?_⟩
      · intro i hi
        rw [projection.2.2.1 i hi]
        exact state.selected i hi
      · change [{target:=e+1,arity:=0,height:=sp,isLoop:=false},root]=_
        rw [saved]
  

/-- Actual nested-end step. The root label remains, while AIR constrains
PC, stack, gas, label metadata, and continuing status of the successor. -/
theorem prepared_typed_nested_end_state (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (endOp : tr.cell t r 469=1) (nested : tr.cell t r 639=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (sp : Nat) (root : Label) (state : PreparedTypedState (tr.cell t r) s f fs sp count root)
    (pf : PFunc) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some .end_) (amount : Nat)
    (charge : PreparedWasmCharge pf f.pc amount) (bounded : amount<u64Bound)
    (fee : preparedExecWord64 (tr.cell t r) 502=amount) (enough : amount≤s.gas.g) :
    ∃ s',step cfg p s=.cont s' ∧
      PreparedTypedState (tr.cell t (r+1)) s'
        {f with pc:=f.pc+1,labels:=[root]} fs sp count root ∧
      tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have flags:=prepared_typed_opcode_selected count state.countBound tr t r pub localH (by omega) 3 (by decide) endOp
  have set0:=flags 7 (by decide);have tee0:=flags 8 (by decide)
  change tr.cell t r 684=0 at set0
  change tr.cell t r 685=0 at tee0
  have preserve:=prepared_typed_local_array_preserve count state.countBound tr t r pub localH nonlast set0 tee0
  have localsEq : f.locals=preparedTypedLocalArray (tr.cell t (r+1)) count:=state.locals.trans preserve.symm
  have enoughRow : preparedExecWord64 (tr.cell t r) 502≤preparedExecWord64 (tr.cell t r) 299 := by
    rw [fee,←state.gas];exact enough
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr t r pub (prepared_typed_gas_source count state.countBound) localH nonlast active enoughRow
  have projection:=prepared_typed_nested_end_label count state.countBound tr t r pub localH nonlast active charged endOp nested
  obtain ⟨lab,labels⟩ : ∃ lab,f.labels=[lab,root] := by
    rcases state.labels with h|⟨height,_,_,_,labels⟩
    · rw [nested] at h
      exact False.elim ((by decide : (1:Fp)≠0) h.1)
    · exact ⟨_,labels⟩
  have nextSelected:=prepared_typed_frame_depth count state.countBound tr t r pub localH nonlast 3 (Or.inl rfl) endOp sp state.depth state.selected
  have stack : preparedTypedStack (tr.cell t (r+1)) sp=s.stack := by
    rw [state.stack]
    apply prepared_typed_stack_congr
    intro i hi
    exact prepared_typed_frame_stack_value count state.countBound tr t r pub localH nonlast 3 (Or.inl rfl) endOp i (by have hs:=state.depth;omega)
  have run:=prepared_control_step_nested_end cfg p s f fs pf amount lab root state.frames func code labels charge bounded enough
  let f' : Frame:={f with pc:=f.pc+1,labels:=[root]}
  let s' : St:={s with frames:=f'::fs,gas:={s.gas with g:=s.gas.g-amount}}
  have run' : step cfg p s=.cont s' := by
    simpa only [setFrame,state.frames] using run
  refine ⟨s',run',?_,projection.2.2.2.2.1,projection.2.2.2.2.2⟩
  refine ⟨state.depth,nextSelected,rfl,?_,stack.symm,?_,state.countBound,localsEq,Or.inl ⟨projection.1,rfl⟩⟩
  · change f.pc+1=preparedCodeExecPC (tr.cell t (r+1))
    rw [state.pc,projection.2.2.2.1]
  · change s.gas.g-amount=preparedExecWord64 (tr.cell t (r+1)) 299
    rw [gas,fee,state.gas]

end NearCompression
