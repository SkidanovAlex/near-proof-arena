import NearCompression.PreparedTypedBranchArrays
import NearCompression.PreparedTypedBranchDepth
import NearCompression.PreparedTypedUntaken
import NearCompression.PreparedTypedEqzState
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Both actual br_if paths preserve arbitrary typed live prefixes. -/
theorem prepared_typed_branch_state (count : Nat)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) (branch : tr.cell t r 606=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (sp : Nat) (root : Label) (state : PreparedTypedState (tr.cell t r) s f fs sp count root)
    (pf : PFunc) (func : p.funcs[f.fn]?=some pf) (code : pf.code[f.pc]?=some (.brIf 0))
    (charge : PreparedWasmCharge pf f.pc (preparedExecWord64 (tr.cell t r) 502))
    (bound : preparedExecWord64 (tr.cell t r) 502<u64Bound)
    (enough : preparedExecWord64 (tr.cell t r) 502≤s.gas.g) :
    ∃s' f' sp',step cfg p s=.cont s' ∧ PreparedTypedState (tr.cell t (r+1)) s' f' fs sp' count root ∧
      f'.fn=f.fn ∧ tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have hc:=state.countBound
  have sb:=state.depth
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr t r pub (prepared_typed_gas_source count hc) localH nonlast active
    (by rw [←state.gas];exact enough)
  have present:=prepared_typed_branch_present count hc tr t r pub localH (by omega) active charged branch
  obtain ⟨height,hb,saved,labels⟩ : ∃height,height<9 ∧
      (∀i,i<9 → tr.cell t r (640+i)=if i=height then 1 else 0) ∧
      f.labels=[{target:=preparedControlSavedTarget (tr.cell t r),arity:=0,height:=height,isLoop:=false},root] := by
    rcases state.labels with h|⟨height,hb,_,saved,labels⟩
    · rw [present] at h
      exact False.elim ((by decide:(1:Fp)≠0) h.1)
    · exact ⟨height,hb,saved,labels⟩
  have lt:=prepared_typed_branch_height_lt count hc tr t r pub localH (by omega) active charged branch sp height sb hb state.selected saved
  obtain ⟨positive,tag,condition⟩:=prepared_typed_branch_operand count hc tr t r pub localH (by omega) active charged branch sp sb state.selected
  have wordEq:=prepared_typed_stack_i32_word count hc tr t r pub localH (by omega) (sp-1) (by omega) tag
  have wordBound:=prepared_typed_stack_i32_bound count hc tr t r pub localH (by omega) (sp-1) (by omega) tag
  rw [wordEq] at wordBound
  let values:=preparedTypedStack (tr.cell t r) (sp-1)
  let value:=UInt32.ofNat (preparedExecStackWord (tr.cell t r) (sp-1))
  have valueNat:value.toNat=preparedExecStackWord (tr.cell t r) (sp-1):=Nat.mod_eq_of_lt wordBound
  have stack:s.stack=values.push (.i32 value) := by
    rw [state.stack]
    have e:=prepared_typed_stack_succ (tr.cell t r) (sp-1)
    rw [show sp-1+1=sp by omega] at e
    rw [e]
    simp only [preparedTypedStackValue,tag,ite_true,wordEq]
    rfl
  have flags:=prepared_typed_opcode_selected count hc tr t r pub localH (by omega) 5 (by decide) branch
  have set0:=flags 7 (by decide);have tee0:=flags 8 (by decide);have end0:=flags 3 (by decide)
  change tr.cell t r 684=0 at set0
  change tr.cell t r 685=0 at tee0
  change tr.cell t r 469=0 at end0
  have localsEq:=prepared_typed_local_array_preserve count hc tr t r pub localH nonlast set0 tee0
  have run:=prepared_control_step_br_if cfg p s f fs pf _ values value _ height root state.frames func code labels stack charge bound enough
  by_cases zero:tr.cell t r 681=0
  · have valueZero:value.toNat=0:=valueNat.trans (condition.mp zero)
    simp only [valueZero,ite_true] at run
    have depth:=prepared_typed_branch_depth count hc tr t r pub localH nonlast active charged branch false zero height hb saved sp sb positive state.selected
    have array:=prepared_typed_branch_array count hc tr t r pub localH nonlast active charged branch false zero sp height sb hb lt state.selected saved
    change preparedTypedStack (tr.cell t (r+1)) (sp-1)=values at array
    have pc:=prepared_typed_untaken_pc_label count hc tr t r pub localH nonlast active charged branch zero
    let f':Frame:={f with pc:=f.pc+1}
    let s':St:={s with frames:=f'::fs,stack:=values,gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell t r) 502}}
    refine ⟨s',f',sp-1,?_,?_,rfl,pc.2.1,pc.2.2.1⟩
    · simpa only [setFrame,state.frames] using run
    · refine ⟨by omega,depth,rfl,?_,array.symm,?_,hc,?_,?_⟩
      · change f.pc+1=preparedCodeExecPC (tr.cell t (r+1));rw [pc.1,state.pc]
      · change s.gas.g-preparedExecWord64 (tr.cell t r) 502=preparedExecWord64 (tr.cell t (r+1)) 299
        rw [gas,state.gas]
      · change f.locals=preparedTypedLocalArray (tr.cell t (r+1)) count
        rw [localsEq,state.locals]
      · exact prepared_control_labels_transport _ _ _ _ root state.labels rfl pc.2.2.2.1 pc.2.2.2.2.1 pc.2.2.2.2.2
  · have bit:=prepared_typed_source_boolean count hc tr t r pub localH (by omega) 681 (by decide) (by decide) (by decide)
    have one:tr.cell t r 681=1:=by
      have nz:(tr.cell t r 681).toNat≠0:=fun h=>zero (Fp.ext h)
      apply Fp.ext
      change (tr.cell t r 681).toNat=1
      omega
    have valueNonzero:value.toNat≠0:=by intro h;apply zero;exact condition.mpr (valueNat.symm.trans h)
    simp only [valueNonzero,ite_false] at run
    have depth:=prepared_typed_branch_depth count hc tr t r pub localH nonlast active charged branch true one height hb saved sp sb positive state.selected
    have array:=prepared_typed_branch_array count hc tr t r pub localH nonlast active charged branch true one sp height sb hb lt state.selected saved
    change preparedTypedStack (tr.cell t (r+1)) height=values.extract 0 height at array
    have pc:=prepared_typed_taken_pc count hc tr t r pub localH nonlast active charged branch one
    have nextLabel:=prepared_typed_taken_label count hc tr t r pub localH nonlast active charged branch one
    have status:=prepared_typed_continue_status count hc tr t r pub localH nonlast active charged (by rw [end0];grind)
    let f':Frame:={f with pc:=preparedControlSavedTarget (tr.cell t r),labels:=[root]}
    let s':St:={s with frames:=f'::fs,stack:=values.extract 0 height,gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell t r) 502}}
    refine ⟨s',f',height,?_,?_,rfl,status.2.1,status.2.2⟩
    · simpa only [setFrame,state.frames] using run
    · refine ⟨hb,depth,rfl,pc.symm,array.symm,?_,hc,?_,Or.inl ⟨nextLabel.1,rfl⟩⟩
      · change s.gas.g-preparedExecWord64 (tr.cell t r) 502=preparedExecWord64 (tr.cell t (r+1)) 299
        rw [gas,state.gas]
      · change f.locals=preparedTypedLocalArray (tr.cell t (r+1)) count
        rw [localsEq,state.locals]
end NearCompression
