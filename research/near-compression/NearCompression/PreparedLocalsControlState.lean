import NearCompression.PreparedLocalsBlock
import NearCompression.PreparedLocalsFrameStack
import NearCompression.PreparedLocalsControlPreserve
import NearCompression.PreparedLocalsGas
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
theorem prepared_locals_block_state (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (block : tr.cell t r 605=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (sp : Nat) (root : Label) (state : PreparedLocalsState (tr.cell t r) s f fs sp count root)
    (pf : PFunc) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some (.block none)) (e amount : Nat)
    (target : pf.endOf[f.pc]?=some e)
    (targetRow : (preparedCodeLimb (tr.cell t r) 607).toNat+65536*(preparedCodeLimb (tr.cell t r) 623).toNat=e+1)
    (charge : PreparedWasmCharge pf f.pc amount) (bounded : amount<u64Bound)
    (fee : preparedExecWord64 (tr.cell t r) 502=amount) (enough : amount≤s.gas.g) :
    ∃ s',step cfg p s=.cont s' ∧
      PreparedLocalsState (tr.cell t (r+1)) s'
        {f with pc:=f.pc+1,labels:=[{target:=e+1,arity:=0,height:=sp,isLoop:=false},root]} fs sp count root ∧
      tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have preserve:=prepared_locals_control_array_preserved count state.2.1 tr t r pub localH nonlast 4 (by decide) block
  have localsEq : f.locals=preparedLocalsArray (tr.cell t (r+1)) count:=state.2.2.trans preserve.symm
  have enoughRow : preparedExecWord64 (tr.cell t r) 502≤preparedExecWord64 (tr.cell t r) 299 := by
    rw [fee,←state.1.1.gas];exact enough
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr t r pub (prepared_locals_gas_source count) localH nonlast active enoughRow
  have projection:=prepared_locals_block_label count tr t r pub localH nonlast active charged block
  have labels : f.labels=[root] := by
    rcases state.1.2 with h|⟨height,_,present,_,_⟩
    · exact h.2
    · rw [projection.1] at present
      exact False.elim ((by decide : (0:Fp)≠1) present)
  obtain ⟨sp',bound,selected,nextSelected⟩:=prepared_locals_frame_sp count tr t r pub localH nonlast 4 (Or.inr rfl) block
  have eq : sp'=sp := by
    have a:=selected sp' bound
    have b:=state.1.1.selected sp' bound
    rw [if_pos rfl] at a
    rw [a] at b
    by_cases eq:sp'=sp
    · exact eq
    · simp only [eq,ite_false] at b
      exact False.elim ((by decide : (1:Fp)≠0) b)
  subst sp'
  have stack : preparedWasmStack (preparedExecGhostRow (tr.cell t (r+1))) sp=s.stack := by
    rw [state.1.1.stack]
    apply prepared_wasm_stack_congr
    intro i hi
    exact prepared_locals_frame_stack count tr t r pub localH nonlast 4 (Or.inr rfl) block i (by omega)
  have size : s.stack.size=sp := by rw [state.1.1.stack,prepared_control_stack_size]
  have saved : preparedControlSavedTarget (tr.cell t (r+1))=e+1 := by
    have l:=projection.2.2.2.1 0 (by decide)
    have h:=projection.2.2.2.1 1 (by decide)
    simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one,Nat.reduceAdd] at l h
    unfold preparedControlSavedTarget
    rw [l,h];exact targetRow
  have run:=prepared_control_step_block cfg p s f fs pf amount e state.1.1.frames func code target charge bounded enough
  rw [size,labels] at run
  let f' : Frame:={f with pc:=f.pc+1,labels:=[{target:=e+1,arity:=0,height:=sp,isLoop:=false},root]}
  let s' : St:={s with frames:=f'::fs,gas:={s.gas with g:=s.gas.g-amount}}
  have run' : step cfg p s=.cont s' := by
    simpa only [setFrame,state.1.1.frames] using run
  refine ⟨s',run',⟨⟨?_,?_⟩,state.2.1,localsEq⟩,projection.2.2.2.2.2.1,projection.2.2.2.2.2.2⟩
  · refine ⟨state.1.1.depth,nextSelected,rfl,?_,stack.symm,?_⟩
    · change f.pc+1=preparedCodeExecPC (tr.cell t (r+1))
      rw [state.1.1.pc,projection.2.2.2.2.1]
    · change s.gas.g-amount=preparedExecWord64 (tr.cell t (r+1)) 299
      rw [gas,fee,state.1.1.gas]
  · right
    refine ⟨sp,state.1.1.depth,projection.2.1,?_,?_⟩
    · intro i hi
      rw [projection.2.2.1 i hi]
      exact state.1.1.selected i hi
    · change [{target:=e+1,arity:=0,height:=sp,isLoop:=false},root]=_
      rw [saved]

/-- Actual nested-end step. The root label remains, while AIR constrains
PC, stack, gas, label metadata, and continuing status of the successor. -/
theorem prepared_locals_nested_end_state (count : Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (endOp : tr.cell t r 469=1) (nested : tr.cell t r 639=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (sp : Nat) (root : Label) (state : PreparedLocalsState (tr.cell t r) s f fs sp count root)
    (pf : PFunc) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some .end_) (amount : Nat)
    (charge : PreparedWasmCharge pf f.pc amount) (bounded : amount<u64Bound)
    (fee : preparedExecWord64 (tr.cell t r) 502=amount) (enough : amount≤s.gas.g) :
    ∃ s',step cfg p s=.cont s' ∧
      PreparedLocalsState (tr.cell t (r+1)) s'
        {f with pc:=f.pc+1,labels:=[root]} fs sp count root ∧
      tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have preserve:=prepared_locals_control_array_preserved count state.2.1 tr t r pub localH nonlast 3 (by decide) endOp
  have localsEq : f.locals=preparedLocalsArray (tr.cell t (r+1)) count:=state.2.2.trans preserve.symm
  have enoughRow : preparedExecWord64 (tr.cell t r) 502≤preparedExecWord64 (tr.cell t r) 299 := by
    rw [fee,←state.1.1.gas];exact enough
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr t r pub (prepared_locals_gas_source count) localH nonlast active enoughRow
  have projection:=prepared_locals_nested_end_label count tr t r pub localH nonlast active charged endOp nested
  obtain ⟨lab,labels⟩ : ∃ lab,f.labels=[lab,root] := by
    rcases state.1.2 with h|⟨height,_,_,_,labels⟩
    · rw [nested] at h
      exact False.elim ((by decide : (1:Fp)≠0) h.1)
    · exact ⟨_,labels⟩
  obtain ⟨sp',bound,selected,nextSelected⟩:=prepared_locals_frame_sp count tr t r pub localH nonlast 3 (Or.inl rfl) endOp
  have eq : sp'=sp := by
    have a:=selected sp' bound
    have b:=state.1.1.selected sp' bound
    rw [if_pos rfl] at a
    rw [a] at b
    by_cases eq:sp'=sp
    · exact eq
    · simp only [eq,ite_false] at b
      exact False.elim ((by decide : (1:Fp)≠0) b)
  subst sp'
  have stack : preparedWasmStack (preparedExecGhostRow (tr.cell t (r+1))) sp=s.stack := by
    rw [state.1.1.stack]
    apply prepared_wasm_stack_congr
    intro i hi
    exact prepared_locals_frame_stack count tr t r pub localH nonlast 3 (Or.inl rfl) endOp i (by omega)
  have run:=prepared_control_step_nested_end cfg p s f fs pf amount lab root state.1.1.frames func code labels charge bounded enough
  let f' : Frame:={f with pc:=f.pc+1,labels:=[root]}
  let s' : St:={s with frames:=f'::fs,gas:={s.gas with g:=s.gas.g-amount}}
  have run' : step cfg p s=.cont s' := by
    simpa only [setFrame,state.1.1.frames] using run
  refine ⟨s',run',⟨⟨?_,Or.inl ⟨projection.1,rfl⟩⟩,state.2.1,localsEq⟩,projection.2.2.2.2.1,projection.2.2.2.2.2⟩
  refine ⟨state.1.1.depth,nextSelected,rfl,?_,stack.symm,?_⟩
  · change f.pc+1=preparedCodeExecPC (tr.cell t (r+1))
    rw [state.1.1.pc,projection.2.2.2.1]
  · change s.gas.g-amount=preparedExecWord64 (tr.cell t (r+1)) 299
    rw [gas,fee,state.1.1.gas]

end NearCompression
