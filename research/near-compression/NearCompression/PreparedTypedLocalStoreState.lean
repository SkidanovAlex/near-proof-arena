import NearCompression.PreparedTypedLocalGetState
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem prepared_typed_local_set_state (count : Nat)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (opcode : tr.cell t r 684=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (sp : Nat) (root : Label) (state : PreparedTypedState (tr.cell t r) s f fs sp count root)
    (pf : PFunc) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some (.localSet ((preparedCodeLimb (tr.cell t r) 470).toNat+
      65536*(preparedCodeLimb (tr.cell t r) 486).toNat)))
    (charge : PreparedWasmCharge pf f.pc (preparedExecWord64 (tr.cell t r) 502))
    (feeBound : preparedExecWord64 (tr.cell t r) 502<u64Bound)
    (enough : preparedExecWord64 (tr.cell t r) 502≤s.gas.g) :
    ∃s',step cfg p s=.cont s' ∧
      PreparedTypedState (tr.cell t (r+1)) s' {f with pc:=f.pc+1,locals:=f.locals.set! ((preparedCodeLimb (tr.cell t r) 470).toNat+65536*(preparedCodeLimb (tr.cell t r) 486).toNat) (preparedTypedStackValue (tr.cell t r) (sp-1))} fs (sp-1) count root ∧
      tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have hc:=state.countBound
  have gas:=prepared_control_gas_success _ tr t r pub (prepared_typed_gas_source count state.countBound) localH nonlast active
    (by rw [←state.gas];exact enough)
  have flags:=prepared_typed_opcode_selected count state.countBound tr t r pub localH (by omega) 7 (by decide) opcode
  have end0:=flags 3 (by decide);have block0:=flags 4 (by decide);have branch0:=flags 5 (by decide)
  have get0:=flags 6 (by decide)
  have other:=flags 8 (by decide)
  change tr.cell t r 469=0 at end0
  change tr.cell t r 605=0 at block0
  change tr.cell t r 606=0 at branch0
  change tr.cell t r 683=0 at get0
  change tr.cell t r 685=0 at other
  have old : ∀i,i<3 → tr.cell t r (466+i)=0 := by
    intro i hi
    have cases : i=0 ∨ i=1 ∨ i=2:=by omega
    rcases cases with rfl|rfl|rfl
    · exact flags 0 (by decide)
    · exact flags 1 (by decide)
    · exact flags 2 (by decide)
  have typed : ∀i,i<3 → tr.cell t r (1280+i)=0 := by
    intro i hi
    have cases : i=0 ∨ i=1 ∨ i=2:=by omega
    rcases cases with rfl|rfl|rfl
    · exact flags 9 (by decide)
    · exact flags 10 (by decide)
    · exact flags 11 (by decide)
  have op : tr.cell t r 683+(tr.cell t r 684+tr.cell t r 685)=1 := by rw [get0,opcode,other];grind
  obtain ⟨index,ib,selected⟩:=prepared_typed_local_selected count state.countBound tr t r pub localH (by omega) op
  have indexEq:=prepared_typed_local_index count state.countBound tr t r pub localH (by omega) op index (by omega) selected
  obtain ⟨room,next,nb,delta,hot⟩:=prepared_typed_local_depth .set count state.countBound tr t r pub localH nonlast active gas.1 old branch0 typed get0 opcode other sp state.depth state.selected
  have nextEq:next=(sp-1):=by simp only [reduceCtorEq,ite_true,ite_false] at delta;omega
  subst next
  change 0<sp at room
  have values:=prepared_typed_local_stack_value .set count state.countBound tr t r pub localH nonlast active gas.1 old branch0 typed get0 opcode sp index state.depth (by omega) state.selected selected
  have stackEq:=prepared_typed_local_stack_arrays .set (tr.cell t r) (tr.cell t (r+1)) sp index ⟨room,state.depth⟩ values
  change preparedTypedStack (tr.cell t (r+1)) (sp-1)=(preparedTypedStack (tr.cell t r) sp).pop at stackEq
  have pc:=prepared_typed_pc_label count state.countBound tr t r pub localH nonlast active gas.1 end0 block0 branch0
  have write : tr.cell t r 684+tr.cell t r 685=1:=by rw [opcode,other];grind
  have localsEq:=prepared_typed_local_array_write count hc tr t r pub localH nonlast active gas.1 write sp index state.depth room ib state.selected selected
  have before : s.stack=(preparedTypedStack (tr.cell t r) (sp-1)).push (preparedTypedStackValue (tr.cell t r) (sp-1)) := by
    rw [state.stack]
    have eq:sp=(sp-1)+1:=by omega
    have h:=prepared_typed_stack_succ (tr.cell t r) (sp-1)
    rw [←eq] at h
    exact h
  rw [indexEq] at code
  rw [indexEq]
  let successor : St:={s with
    frames:=({f with pc:=f.pc+1,locals:=f.locals.set! index (preparedTypedStackValue (tr.cell t r) (sp-1))}::fs),
    stack:=preparedTypedStack (tr.cell t (r+1)) (sp-1),gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell t r) 502}}
  refine ⟨successor,?_,?_,pc.2.1,pc.2.2.1⟩
  · rw [prepared_wasm_step_charge cfg p s f fs pf (.localSet index) _ state.frames func code charge feeBound enough,
      prepared_locals_exec_set cfg p {s with gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell t r) 502}} f pf index _ _ (show s.stack=_ from before)]
    dsimp only [setFrame,successor]
    have popEq : preparedTypedStack (tr.cell t (r+1)) (sp-1)=preparedTypedStack (tr.cell t r) (sp-1) := by
      rw [stackEq,←state.stack,before,Array.pop_push]
    rw [popEq]
    simp only [state.frames]
  · refine ⟨nb,hot,rfl,?_,rfl,?_,state.countBound,?_,?_⟩
    · change f.pc+1=preparedCodeExecPC (tr.cell t (r+1))
      rw [pc.1,state.pc]
    · change s.gas.g-preparedExecWord64 (tr.cell t r) 502=preparedExecWord64 (tr.cell t (r+1)) 299
      rw [gas.2,state.gas]
    · change f.locals.set! index (preparedTypedStackValue (tr.cell t r) (sp-1))=preparedTypedLocalArray (tr.cell t (r+1)) count
      rw [localsEq,state.locals]
    · exact prepared_control_labels_transport _ _ _ _ root state.labels rfl pc.2.2.2.1 pc.2.2.2.2.1 pc.2.2.2.2.2

theorem prepared_typed_local_tee_state (count : Nat)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (opcode : tr.cell t r 685=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (sp : Nat) (root : Label) (state : PreparedTypedState (tr.cell t r) s f fs sp count root)
    (pf : PFunc) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some (.localTee ((preparedCodeLimb (tr.cell t r) 470).toNat+
      65536*(preparedCodeLimb (tr.cell t r) 486).toNat)))
    (charge : PreparedWasmCharge pf f.pc (preparedExecWord64 (tr.cell t r) 502))
    (feeBound : preparedExecWord64 (tr.cell t r) 502<u64Bound)
    (enough : preparedExecWord64 (tr.cell t r) 502≤s.gas.g) :
    ∃s',step cfg p s=.cont s' ∧
      PreparedTypedState (tr.cell t (r+1)) s' {f with pc:=f.pc+1,locals:=f.locals.set! ((preparedCodeLimb (tr.cell t r) 470).toNat+65536*(preparedCodeLimb (tr.cell t r) 486).toNat) (preparedTypedStackValue (tr.cell t r) (sp-1))} fs sp count root ∧
      tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have hc:=state.countBound
  have gas:=prepared_control_gas_success _ tr t r pub (prepared_typed_gas_source count state.countBound) localH nonlast active
    (by rw [←state.gas];exact enough)
  have flags:=prepared_typed_opcode_selected count state.countBound tr t r pub localH (by omega) 8 (by decide) opcode
  have end0:=flags 3 (by decide);have block0:=flags 4 (by decide);have branch0:=flags 5 (by decide)
  have get0:=flags 6 (by decide)
  have other:=flags 7 (by decide)
  change tr.cell t r 469=0 at end0
  change tr.cell t r 605=0 at block0
  change tr.cell t r 606=0 at branch0
  change tr.cell t r 683=0 at get0
  change tr.cell t r 684=0 at other
  have old : ∀i,i<3 → tr.cell t r (466+i)=0 := by
    intro i hi
    have cases : i=0 ∨ i=1 ∨ i=2:=by omega
    rcases cases with rfl|rfl|rfl
    · exact flags 0 (by decide)
    · exact flags 1 (by decide)
    · exact flags 2 (by decide)
  have typed : ∀i,i<3 → tr.cell t r (1280+i)=0 := by
    intro i hi
    have cases : i=0 ∨ i=1 ∨ i=2:=by omega
    rcases cases with rfl|rfl|rfl
    · exact flags 9 (by decide)
    · exact flags 10 (by decide)
    · exact flags 11 (by decide)
  have op : tr.cell t r 683+(tr.cell t r 684+tr.cell t r 685)=1 := by rw [get0,opcode,other];grind
  obtain ⟨index,ib,selected⟩:=prepared_typed_local_selected count state.countBound tr t r pub localH (by omega) op
  have indexEq:=prepared_typed_local_index count state.countBound tr t r pub localH (by omega) op index (by omega) selected
  obtain ⟨room,next,nb,delta,hot⟩:=prepared_typed_local_depth .tee count state.countBound tr t r pub localH nonlast active gas.1 old branch0 typed get0 other opcode sp state.depth state.selected
  have nextEq:next=sp:=by simp only [reduceCtorEq,ite_true,ite_false] at delta;omega
  subst next
  change 0<sp at room
  have values:=prepared_typed_local_stack_value .tee count state.countBound tr t r pub localH nonlast active gas.1 old branch0 typed get0 other sp index state.depth (by omega) state.selected selected
  have stackEq:=prepared_typed_local_stack_arrays .tee (tr.cell t r) (tr.cell t (r+1)) sp index ⟨room,state.depth⟩ values
  change preparedTypedStack (tr.cell t (r+1)) sp=preparedTypedStack (tr.cell t r) sp at stackEq
  have pc:=prepared_typed_pc_label count state.countBound tr t r pub localH nonlast active gas.1 end0 block0 branch0
  have write : tr.cell t r 684+tr.cell t r 685=1:=by rw [opcode,other];grind
  have localsEq:=prepared_typed_local_array_write count hc tr t r pub localH nonlast active gas.1 write sp index state.depth room ib state.selected selected
  have before : s.stack=(preparedTypedStack (tr.cell t r) (sp-1)).push (preparedTypedStackValue (tr.cell t r) (sp-1)) := by
    rw [state.stack]
    have eq:sp=(sp-1)+1:=by omega
    have h:=prepared_typed_stack_succ (tr.cell t r) (sp-1)
    rw [←eq] at h
    exact h
  rw [indexEq] at code
  rw [indexEq]
  let successor : St:={s with
    frames:=({f with pc:=f.pc+1,locals:=f.locals.set! index (preparedTypedStackValue (tr.cell t r) (sp-1))}::fs),
    stack:=preparedTypedStack (tr.cell t (r+1)) sp,gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell t r) 502}}
  refine ⟨successor,?_,?_,pc.2.1,pc.2.2.1⟩
  · rw [prepared_wasm_step_charge cfg p s f fs pf (.localTee index) _ state.frames func code charge feeBound enough,
      prepared_locals_exec_tee cfg p {s with gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell t r) 502}} f pf index _ _ (show s.stack=_ from before)]
    dsimp only [setFrame,successor]
    rw [stackEq,←state.stack]
    simp only [state.frames]
  · refine ⟨nb,hot,rfl,?_,rfl,?_,state.countBound,?_,?_⟩
    · change f.pc+1=preparedCodeExecPC (tr.cell t (r+1))
      rw [pc.1,state.pc]
    · change s.gas.g-preparedExecWord64 (tr.cell t r) 502=preparedExecWord64 (tr.cell t (r+1)) 299
      rw [gas.2,state.gas]
    · change f.locals.set! index (preparedTypedStackValue (tr.cell t r) (sp-1))=preparedTypedLocalArray (tr.cell t (r+1)) count
      rw [localsEq,state.locals]
    · exact prepared_control_labels_transport _ _ _ _ root state.labels rfl pc.2.2.2.1 pc.2.2.2.2.1 pc.2.2.2.2.2
end NearCompression
