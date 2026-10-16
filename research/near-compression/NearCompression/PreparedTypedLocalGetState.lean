import NearCompression.PreparedTypedLocalStackValues
import NearCompression.PreparedTypedLocalDepth
import NearCompression.PreparedTypedEqzState
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Actual local.get successor, with explicit prepared code/charge context.
The selected local, stack write, depth, PC, gas, labels and locals all come
from the concrete literal AIR rather than a supplied successor certificate. -/
theorem prepared_typed_local_get_state (count : Nat)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (opcode : tr.cell t r 683=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (sp : Nat) (root : Label) (state : PreparedTypedState (tr.cell t r) s f fs sp count root)
    (pf : PFunc) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some (.localGet ((preparedCodeLimb (tr.cell t r) 470).toNat+
      65536*(preparedCodeLimb (tr.cell t r) 486).toNat)))
    (charge : PreparedWasmCharge pf f.pc (preparedExecWord64 (tr.cell t r) 502))
    (feeBound : preparedExecWord64 (tr.cell t r) 502<u64Bound)
    (enough : preparedExecWord64 (tr.cell t r) 502≤s.gas.g) :
    ∃s',step cfg p s=.cont s' ∧
      PreparedTypedState (tr.cell t (r+1)) s' {f with pc:=f.pc+1} fs (sp+1) count root ∧
      tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have hc:=state.countBound
  have gas:=prepared_control_gas_success _ tr t r pub (prepared_typed_gas_source count state.countBound) localH nonlast active
    (by rw [←state.gas];exact enough)
  have flags:=prepared_typed_opcode_selected count state.countBound tr t r pub localH (by omega) 6 (by decide) opcode
  have end0:=flags 3 (by decide);have block0:=flags 4 (by decide);have branch0:=flags 5 (by decide)
  have set0:=flags 7 (by decide);have tee0:=flags 8 (by decide)
  change tr.cell t r 469=0 at end0
  change tr.cell t r 605=0 at block0
  change tr.cell t r 606=0 at branch0
  change tr.cell t r 684=0 at set0
  change tr.cell t r 685=0 at tee0
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
  have op : tr.cell t r 683+(tr.cell t r 684+tr.cell t r 685)=1 := by rw [opcode,set0,tee0];grind
  obtain ⟨index,ib,selected⟩:=prepared_typed_local_selected count state.countBound tr t r pub localH (by omega) op
  have indexEq:=prepared_typed_local_index count state.countBound tr t r pub localH (by omega) op index (by omega) selected
  obtain ⟨room,next,nb,delta,hot⟩:=prepared_typed_local_depth .get count state.countBound tr t r pub localH nonlast active gas.1 old branch0 typed opcode set0 tee0 sp state.depth state.selected
  have nextEq:next=sp+1:=by simpa using delta
  subst next
  have values:=prepared_typed_local_stack_value .get count state.countBound tr t r pub localH nonlast active gas.1 old branch0 typed opcode set0 sp index state.depth (by omega) state.selected selected
  have stackEq:=prepared_typed_local_stack_arrays .get (tr.cell t r) (tr.cell t (r+1)) sp index room values
  change preparedTypedStack (tr.cell t (r+1)) (sp+1)=(preparedTypedStack (tr.cell t r) sp).push _ at stackEq
  have pc:=prepared_typed_pc_label count state.countBound tr t r pub localH nonlast active gas.1 end0 block0 branch0
  have localsEq:=prepared_typed_local_array_preserve count state.countBound tr t r pub localH nonlast set0 tee0
  have lookup : f.locals[index]?=some (preparedTypedLocalValue (tr.cell t r) index) := by
    rw [state.locals]
    exact prepared_typed_local_lookup _ _ _ ib
  rw [indexEq] at code
  let successor : St:={s with
    frames:=({f with pc:=f.pc+1}::fs),
    stack:=preparedTypedStack (tr.cell t (r+1)) (sp+1),gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell t r) 502}}
  refine ⟨successor,?_,?_,pc.2.1,pc.2.2.1⟩
  · rw [prepared_wasm_step_charge cfg p s f fs pf (.localGet index) _ state.frames func code charge feeBound enough,
      prepared_locals_exec_get cfg p _ f pf index _ lookup]
    dsimp only [setFrame,pushV,successor]
    rw [state.stack,←stackEq]
    simp only [state.frames]
  · refine ⟨nb,hot,rfl,?_,rfl,?_,state.countBound,?_,?_⟩
    · change f.pc+1=preparedCodeExecPC (tr.cell t (r+1))
      rw [pc.1,state.pc]
    · change s.gas.g-preparedExecWord64 (tr.cell t r) 502=preparedExecWord64 (tr.cell t (r+1)) 299
      rw [gas.2,state.gas]
    · change f.locals=preparedTypedLocalArray (tr.cell t (r+1)) count
      rw [localsEq,state.locals]
    · exact prepared_control_labels_transport _ _ _ _ root state.labels rfl pc.2.2.2.1 pc.2.2.2.2.1 pc.2.2.2.2.2
end NearCompression
