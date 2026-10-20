import NearCompression.PreparedTypedAdd32Stack
import NearCompression.PreparedTypedAdd32Depth
import NearCompression.PreparedTypedEqzState
import NearCompression.PreparedTypedAdd32Arithmetic
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem pop_i32 (s : St) (value : UInt32) :
    popN (pushV s (.i32 value))=(value.toNat,s) := by simp [popN,popV,pushV]

/-- Full actual i32.add successor. Input frame/code/charge context is explicit;
all successor row fields are derived from the literal constraints. -/
theorem prepared_typed_add32_success_state (count : Nat)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (opcode : tr.cell t r 467=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (sp : Nat) (root : Label) (state : PreparedTypedState (tr.cell t r) s f fs sp count root)
    (pf : PFunc) (func : p.funcs[f.fn]?=some pf) (code : pf.code[f.pc]?=some (.num 0x6A))
    (charge : PreparedWasmCharge pf f.pc (preparedExecWord64 (tr.cell t r) 502))
    (feeBound : preparedExecWord64 (tr.cell t r) 502<u64Bound)
    (enough : preparedExecWord64 (tr.cell t r) 502≤s.gas.g) :
    ∃s',step cfg p s=.cont s' ∧
      PreparedTypedState (tr.cell t (r+1)) s' {f with pc:=f.pc+1} fs (sp-1) count root ∧
      tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have sb:=state.depth
  have gas:=prepared_control_gas_success _ tr t r pub (prepared_typed_gas_source count state.countBound) localH nonlast active
    (by rw [←state.gas];exact enough)
  have operands:=prepared_typed_add32_operands count state.countBound tr t r pub localH (by omega) active gas.1 opcode sp state.depth state.selected
  have depth:=prepared_typed_add32_depth count state.countBound tr t r pub localH nonlast active gas.1 opcode sp state.depth state.selected
  have before : preparedTypedStack (tr.cell t r) sp=
      ((preparedTypedStack (tr.cell t r) (sp-2)).push (.i32 (UInt32.ofNat (preparedTypedStackWord (tr.cell t r) (sp-2))))).push
        (.i32 (UInt32.ofNat (preparedTypedStackWord (tr.cell t r) (sp-1)))) := by
    have a:=prepared_typed_stack_succ (tr.cell t r) (sp-2)
    have b:=prepared_typed_stack_succ (tr.cell t r) (sp-1)
    rw [show sp-1+1=sp by omega] at b
    rw [show sp-2+1=sp-1 by omega] at a
    rw [b,a]
    simp only [preparedTypedStackValue,operands.2.1,operands.2.2,ite_true]
  have after : preparedTypedStack (tr.cell t (r+1)) (sp-1)=
      (preparedTypedStack (tr.cell t r) (sp-2)).push (.i32 (UInt32.ofNat (preparedTypedResultWord (tr.cell t r)))) := by
    have a:=prepared_typed_stack_succ (tr.cell t (r+1)) (sp-2)
    rw [show sp-2+1=sp-1 by omega] at a
    rw [a]
    have prefixEq : preparedTypedStack (tr.cell t (r+1)) (sp-2)=preparedTypedStack (tr.cell t r) (sp-2) := by
      apply prepared_typed_stack_congr
      intro i hi
      simpa only [show ¬i+2=sp by omega,ite_false] using
        prepared_typed_add32_stack_value count state.countBound tr t r pub localH nonlast active gas.1 opcode sp state.depth state.selected i (by omega) (by omega)
    rw [prefixEq]
    have top:=prepared_typed_add32_stack_value count state.countBound tr t r pub localH nonlast active gas.1 opcode sp state.depth state.selected (sp-2) (by omega) (by omega)
    simp only [show sp-2+2=sp by omega,ite_true] at top
    rw [top]
  have flags:=prepared_typed_opcode_selected count state.countBound tr t r pub localH (by omega) 1 (by decide) opcode
  have end0:=flags 3 (by decide);have block0:=flags 4 (by decide);have branch0:=flags 5 (by decide)
  have set0:=flags 7 (by decide);have tee0:=flags 8 (by decide)
  change tr.cell t r 469=0 at end0
  change tr.cell t r 605=0 at block0
  change tr.cell t r 606=0 at branch0
  change tr.cell t r 684=0 at set0
  change tr.cell t r 685=0 at tee0
  have pc:=prepared_typed_pc_label count state.countBound tr t r pub localH nonlast active gas.1 end0 block0 branch0
  have localsEq:=prepared_typed_local_array_preserve count state.countBound tr t r pub localH nonlast set0 tee0
  let leftValue:=preparedTypedStackWord (tr.cell t r) (sp-2)
  let rightValue:=preparedTypedStackWord (tr.cell t r) (sp-1)
  have lb:leftValue<2^32:=prepared_typed_stack_i32_bound count state.countBound tr t r pub localH (by omega) (sp-2) (by omega) operands.2.1
  have rb:rightValue<2^32:=prepared_typed_stack_i32_bound count state.countBound tr t r pub localH (by omega) (sp-1) (by omega) operands.2.2
  have arithmetic:=prepared_typed_add32_binop count state.countBound tr t r pub localH (by omega) active gas.1 opcode sp state.depth state.selected
  let base : St:={s with stack:=preparedTypedStack (tr.cell t r) (sp-2),gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell t r) 502}}
  let successor : St:={s with
    frames:=({f with pc:=f.pc+1}::fs),
    stack:=preparedTypedStack (tr.cell t (r+1)) (sp-1),gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell t r) 502}}
  have pushed : pushV (pushV base (.i32 (UInt32.ofNat leftValue))) (.i32 (UInt32.ofNat rightValue))={s with gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell t r) 502}} := by
    dsimp only [pushV,base,leftValue,rightValue]
    rw [←before,←state.stack]
  have execution : exec cfg p (pushV (pushV base (.i32 (UInt32.ofNat leftValue))) (.i32 (UInt32.ofNat rightValue))) f pf (.num 0x6A)=
      .cont (setFrame (pushI32 base (preparedTypedResultWord (tr.cell t r))) {f with pc:=f.pc+1}) := by
    have num : execNum (pushV (pushV base (.i32 (UInt32.ofNat leftValue))) (.i32 (UInt32.ofNat rightValue))) 0x6A=
        .ok (pushI32 base (preparedTypedResultWord (tr.cell t r))) := by
      simp [execNum,pop_i32,Nat.mod_eq_of_lt lb,Nat.mod_eq_of_lt rb,
        leftValue,rightValue,arithmetic,pure,Except.pure]
    simp only [exec,num]
  refine ⟨successor,?_,?_,pc.2.1,pc.2.2.1⟩
  · rw [prepared_wasm_step_charge cfg p s f fs pf (.num 0x6A) _ state.frames func code charge feeBound enough,←pushed,execution]
    dsimp only [successor,setFrame,pushV,pushI32,base,leftValue,rightValue]
    rw [after]
    simp only [state.frames]
  · refine ⟨by omega,depth.2,rfl,?_,rfl,?_,state.countBound,?_,?_⟩
    · change f.pc+1=preparedCodeExecPC (tr.cell t (r+1))
      rw [pc.1,state.pc]
    · change s.gas.g-preparedExecWord64 (tr.cell t r) 502=preparedExecWord64 (tr.cell t (r+1)) 299
      rw [gas.2,state.gas]
    · change f.locals=preparedTypedLocalArray (tr.cell t (r+1)) count
      rw [localsEq,state.locals]
    · exact prepared_control_labels_transport _ _ _ _ root state.labels rfl pc.2.2.2.1 pc.2.2.2.2.1 pc.2.2.2.2.2
end NearCompression
