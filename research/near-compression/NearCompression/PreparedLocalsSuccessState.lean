import NearCompression.PreparedLocalsStackState
import NearCompression.PreparedLocalsSequential
import NearCompression.PreparedLocalsGas
import NearCompression.PreparedControlLegacyState
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536

/-- Full successor relation for the three local instructions. Code/charge and
opcode flags are explicit input interfaces; every successor field comes from
the literal locals AIR rather than a supplied successor certificate. -/
theorem prepared_locals_success_state (kind : PreparedLocalOp) (count : Nat)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedLocalsLiteralExecTable count) tr t pub)
    (nonlast : r+1<tr.height t) (active : tr.cell t r 41=0)
    (old : ∀i,i<4 → tr.cell t r (466+i)=0)
    (block : tr.cell t r 605=0) (branch : tr.cell t r 606=0)
    (get : tr.cell t r 683=if kind=.get then 1 else 0)
    (set : tr.cell t r 684=if kind=.set then 1 else 0)
    (tee : tr.cell t r 685=if kind=.tee then 1 else 0)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (sp index : Nat) (root : Label)
    (state : PreparedLocalsState (tr.cell t r) s f fs sp count root)
    (valid : index<count) (selected : ∀j,j<4 → tr.cell t r (814+j)=if j=index then 1 else 0)
    (pf : PFunc) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some (kind.instr index))
    (charge : PreparedWasmCharge pf f.pc (preparedExecWord64 (tr.cell t r) 502))
    (feeBound : preparedExecWord64 (tr.cell t r) 502<u64Bound)
    (enough : preparedExecWord64 (tr.cell t r) 502≤s.gas.g) :
    ∃ s', step cfg p s=.cont s' ∧
      PreparedLocalsState (tr.cell t (r+1)) s'
        {f with pc:=f.pc+1,locals:=preparedLocalsArray (tr.cell t (r+1)) count}
        fs (preparedLocalsNextDepth kind sp) count root ∧
      tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have gas:=prepared_control_gas_success _ tr t r pub (prepared_locals_gas_source count) localH nonlast active
    (by rw [←state.1.1.gas];exact enough)
  have projection:=prepared_locals_stack_array kind count tr t r pub localH nonlast active gas.1
    (fun i hi=>old i (by omega)) branch get set tee sp index state.1.1.depth (by have h:=state.2.1;omega)
    state.1.1.selected selected
  have pc:=prepared_locals_pc_label count tr t r pub localH nonlast active gas.1 (old 3 (by decide)) block branch
  let f' : Frame:={f with pc:=f.pc+1,locals:=preparedLocalsArray (tr.cell t (r+1)) count}
  let s' : St:={s with
    frames:=f'::fs
    stack:=preparedWasmStack (preparedExecGhostRow (tr.cell t (r+1))) (preparedLocalsNextDepth kind sp)
    gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell t r) 502}}
  refine ⟨s',?_,?_,pc.2.1,pc.2.2.1⟩
  · cases kind with
    | get =>
      have preserve:=prepared_locals_array_preserved count state.2.1 tr t r pub localH nonlast (by
        intro slot hs
        change preparedLocalsSuccess.eval tr t r pub*((tr.cell t r 684+tr.cell t r 685)*tr.cell t r (814+slot))=0
        rw [set,tee];simp only [reduceCtorEq,ite_false];grind)
      have localsEq : preparedLocalsArray (tr.cell t (r+1)) count=f.locals := preserve.trans state.2.2.symm
      have lookup : f.locals[index]?=some (.i32 (UInt32.ofNat (preparedLocalsWord (tr.cell t r) index))) := by
        rw [state.2.2];exact prepared_locals_lookup _ _ _ valid
      rw [prepared_locals_step_charge cfg p s f fs pf .get index _ state.1.1.frames func code charge feeBound enough]
      simp only [PreparedLocalOp.instr]
      rw [prepared_locals_exec_get cfg p _ f pf index _ lookup]
      dsimp only [s',f']
      rw [projection.2.2.2,←state.1.1.stack,localsEq]
      simp only [setFrame,pushV,state.1.1.frames]
    | set =>
      have run:=prepared_locals_frame_write false count tr t r pub localH nonlast active gas.1
        (by rw [set,tee];simp only [reduceCtorEq,ite_true,ite_false];grind)
        cfg p s f fs sp index _ root state (by simpa only [reduceCtorEq,ite_false] using projection.1)
        valid selected pf func code charge feeBound enough
      dsimp only [s',f']
      rw [projection.2.2.2,←state.1.1.stack]
      exact run
    | tee =>
      have run:=prepared_locals_frame_write true count tr t r pub localH nonlast active gas.1
        (by rw [set,tee];simp only [reduceCtorEq,ite_true,ite_false];grind)
        cfg p s f fs sp index _ root state (by simpa only [reduceCtorEq,ite_false] using projection.1)
        valid selected pf func code charge feeBound enough
      dsimp only [s',f']
      rw [projection.2.2.2,←state.1.1.stack]
      exact run
  · refine ⟨⟨?_,?_⟩,state.2.1,rfl⟩
    · refine ⟨projection.2.1,projection.2.2.1,rfl,?_,rfl,?_⟩
      · change f.pc+1=preparedCodeExecPC (tr.cell t (r+1))
        rw [pc.1,state.1.1.pc]
      · change s.gas.g-preparedExecWord64 (tr.cell t r) 502=preparedExecWord64 (tr.cell t (r+1)) 299
        rw [gas.2,state.1.1.gas]
    · exact prepared_control_labels_transport _ _ f f' root state.1.2 rfl pc.2.2.2.1 pc.2.2.2.2.1 pc.2.2.2.2.2
end NearCompression
