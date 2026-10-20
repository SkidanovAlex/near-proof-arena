import NearCompression.PreparedTypedEqzArray
import NearCompression.PreparedTypedLocalPreserve
import NearCompression.PreparedTypedSequential
import NearCompression.PreparedTypedGas
import NearCompression.PreparedTypedStep
import NearCompression.PreparedControlLegacyState
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Mixed-width state relation. Prepared code/type provenance is a separate
checked interface; the operand stack and locals retain actual Val tags. -/
structure PreparedTypedState (row : Nat→Fp) (s : St) (f : Frame)
    (fs : List Frame) (sp count : Nat) (root : Label) : Prop where
  depth : sp<9
  selected : ∀i,i<9 → row (32+i)=if i=sp then 1 else 0
  frames : s.frames=f::fs
  pc : f.pc=preparedCodeExecPC row
  stack : s.stack=preparedTypedStack row sp
  gas : s.gas.g=preparedExecWord64 row 299
  countBound : count≤4
  locals : f.locals=preparedTypedLocalArray row count
  labels : PreparedControlLabels row f root

/-- Full actual eqz successor. Input frame/code/charge context is explicit;
all successor row fields are derived from the literal constraints. -/
theorem prepared_typed_eqz_success_state (count : Nat)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (opcode : tr.cell t r 1282=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (sp : Nat) (root : Label) (state : PreparedTypedState (tr.cell t r) s f fs sp count root)
    (pf : PFunc) (func : p.funcs[f.fn]?=some pf) (code : pf.code[f.pc]?=some (.num 0x50))
    (charge : PreparedWasmCharge pf f.pc (preparedExecWord64 (tr.cell t r) 502))
    (feeBound : preparedExecWord64 (tr.cell t r) 502<u64Bound)
    (enough : preparedExecWord64 (tr.cell t r) 502≤s.gas.g) :
    ∃s',step cfg p s=.cont s' ∧
      PreparedTypedState (tr.cell t (r+1)) s' {f with pc:=f.pc+1} fs sp count root ∧
      tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have gas:=prepared_control_gas_success _ tr t r pub (prepared_typed_gas_source count state.countBound) localH nonlast active
    (by rw [←state.gas];exact enough)
  obtain ⟨n,nb,pos,hot,nextHot,before,after⟩:=prepared_typed_eqz_arrays count state.countBound tr t r pub localH nonlast active gas.1 opcode
  have eq : n=sp := by
    have a:=state.selected n nb
    have b:=hot n nb
    simp only [ite_true] at b
    by_cases z:n=sp
    · exact z
    · rw [if_neg z,b] at a
      exact False.elim ((by decide : (1:Fp)≠0) a)
  subst n
  have flags:=prepared_typed_opcode_selected count state.countBound tr t r pub localH (by omega) 11 (by decide) opcode
  have end0:=flags 3 (by decide);have block0:=flags 4 (by decide);have branch0:=flags 5 (by decide)
  have set0:=flags 7 (by decide);have tee0:=flags 8 (by decide)
  change tr.cell t r 469=0 at end0
  change tr.cell t r 605=0 at block0
  change tr.cell t r 606=0 at branch0
  change tr.cell t r 684=0 at set0
  change tr.cell t r 685=0 at tee0
  have pc:=prepared_typed_pc_label count state.countBound tr t r pub localH nonlast active gas.1 end0 block0 branch0
  have localsEq:=prepared_typed_local_array_preserve count state.countBound tr t r pub localH nonlast set0 tee0
  let value:=preparedTypedStackWord (tr.cell t r) (sp-1)
  have vb:value<2^64:=prepared_typed_stack_word_bound count state.countBound tr t r pub localH (by omega) (sp-1) (by omega)
  let base : St:={s with stack:=preparedTypedStack (tr.cell t r) (sp-1),gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell t r) 502}}
  let successor : St:={s with
    frames:=({f with pc:=f.pc+1}::fs),
    stack:=preparedTypedStack (tr.cell t (r+1)) sp,gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell t r) 502}}
  have pushed : pushV base (.i64 (UInt64.ofNat value))={s with gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell t r) 502}} := by
    dsimp only [pushV,base,value]
    rw [←before,←state.stack]
  have execution : exec cfg p (pushV base (.i64 (UInt64.ofNat value))) f pf (.num 0x50)=
      .cont (setFrame (pushV base (.i32 (if value=0 then 1 else 0))) {f with pc:=f.pc+1}) := by
    have num : execNum (pushV base (.i64 (UInt64.ofNat value))) 0x50=
        .ok (pushV base (.i32 (if value=0 then 1 else 0))) := by
      by_cases z:value=0
      all_goals simp [execNum,prepared_typed_pop_i64,UInt64.toNat_ofNat,Nat.mod_eq_of_lt vb,Num.b2,z,pure,Except.pure,pushI32]
      all_goals rfl
    simp only [exec,num]
  refine ⟨successor,?_,?_,pc.2.1,pc.2.2.1⟩
  · rw [prepared_wasm_step_charge cfg p s f fs pf (.num 0x50) _ state.frames func code charge feeBound enough,←pushed,execution]
    dsimp only [successor,setFrame,pushV,base,value]
    rw [after]
    simp only [state.frames]
  · refine ⟨state.depth,nextHot,rfl,?_,rfl,?_,state.countBound,?_,?_⟩
    · change f.pc+1=preparedCodeExecPC (tr.cell t (r+1))
      rw [pc.1,state.pc]
    · change s.gas.g-preparedExecWord64 (tr.cell t r) 502=preparedExecWord64 (tr.cell t (r+1)) 299
      rw [gas.2,state.gas]
    · change f.locals=preparedTypedLocalArray (tr.cell t (r+1)) count
      rw [localsEq,state.locals]
    · exact prepared_control_labels_transport _ _ _ _ root state.labels rfl pc.2.2.2.1 pc.2.2.2.2.1 pc.2.2.2.2.2
end NearCompression
