import NearCompression.PreparedControlAuthenticated
import NearCompression.PreparedControlUntaken

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

/-- A false authenticated br_if executes the actual interpreter pop and
continues with the exact constrained state and retained nested block label. -/
theorem prepared_control_setup_untaken_state (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedControlSetupCheck cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (branch : tr.cell 0 r 606=1) (zero : tr.cell 0 r 681=0)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedControlState (tr.cell 0 r) s f fs sp root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    0<sp ∧ ∃ s',step cfg eligible.setup.program s=.cont s' ∧
      PreparedControlState (tr.cell 0 (r+1)) s'
        {f with pc:=f.pc+1} fs (sp-1) root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  have localH:=prepared_control_exec_local count tr pub holds
  obtain ⟨setup,func,checked⟩:=prepared_control_setup_checked cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨_,op,code,charge,bound,ops,_⟩:=prepared_control_authenticated_decode count tr pub holds eligible.func _ checked r (by omega)
  have tag:=ops 5 (by decide)
  change tr.cell 0 r 606=(if 5=op.tag then 1 else 0) at tag
  rw [branch] at tag
  have opEq : op=PreparedControlInstruction.brIf := by
    cases op with
    | brIf => rfl
    | block => exact False.elim ((by decide : (1:Fp)≠0) tag)
    | legacy old => cases old <;> exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  rw [←state.1.pc] at code charge
  have enoughRow : preparedExecWord64 (tr.cell 0 r) 502≤preparedExecWord64 (tr.cell 0 r) 299 := by
    rw [←state.1.gas];exact enough
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr 0 r pub prepared_control_literal_gas_source localH nonlast active enoughRow
  obtain ⟨sp',positive,spBound,selected,nextSelected,condition,words⟩:=
    prepared_control_untaken_stack_projection tr 0 r pub localH nonlast active charged branch zero
  have eq : sp'=sp := by
    have a:=selected sp' spBound
    have b:=state.1.selected sp' spBound
    rw [if_pos rfl] at a
    rw [a] at b
    by_cases eq:sp'=sp
    · exact eq
    · simp only [eq,ite_false] at b
      exact False.elim ((by decide : (1:Fp)≠0) b)
  subst sp'
  have projection:=prepared_control_untaken_pc_label tr 0 r pub localH nonlast active charged branch zero
  have labelOne:=(prepared_control_branch_height tr 0 r pub localH (by omega) active charged branch).1
  obtain ⟨height,hh,present,heightSelected,labels⟩ :
      ∃ height,height<9 ∧ tr.cell 0 r 639=1 ∧
        (∀ i,i<9 → tr.cell 0 r (640+i)=if i=height then 1 else 0) ∧
        f.labels=[{target:=preparedControlSavedTarget (tr.cell 0 r),arity:=0,height:=height,isLoop:=false},root] := by
    rcases state.2 with h|h
    · rw [labelOne] at h
      exact False.elim ((by decide : (1:Fp)≠0) h.1)
    · exact h
  let values:=preparedWasmStack (preparedExecGhostRow (tr.cell 0 r)) (sp-1)
  have stack : s.stack=values.push (.i32 0) := by
    rw [state.1.stack]
    conv => lhs; rw [show sp=(sp-1)+1 by omega]
    change (preparedWasmStack (preparedExecGhostRow (tr.cell 0 r)) (sp-1)).push
      (.i32 (UInt32.ofNat (preparedExecStackWord (tr.cell 0 r) (sp-1))))=_
    rw [condition];rfl
  have nextStack : preparedWasmStack (preparedExecGhostRow (tr.cell 0 (r+1))) (sp-1)=values := by
    apply prepared_wasm_stack_congr
    intro i hi
    have h:=words i (by omega)
    rw [if_neg (by omega)] at h
    exact h
  have run:=prepared_control_step_br_if cfg eligible.setup.program s f fs eligible.func
    (preparedExecWord64 (tr.cell 0 r) 502) values 0 (preparedControlSavedTarget (tr.cell 0 r)) height root
    state.1.frames (by rw [fn];exact func) code labels stack charge bound enough
  simp only [UInt32.toNat_zero,ite_true] at run
  let f' : Frame:={f with pc:=f.pc+1}
  let s' : St:={s with frames:=f'::fs,stack:=values,gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell 0 r) 502}}
  have run' : step cfg eligible.setup.program s=.cont s' := by
    simpa only [setFrame,state.1.frames] using run
  refine ⟨positive,s',run',⟨?_,?_⟩,projection.2.1,projection.2.2.1⟩
  · refine ⟨by omega,nextSelected,rfl,?_,nextStack.symm,?_⟩
    · change f.pc+1=preparedCodeExecPC (tr.cell 0 (r+1))
      rw [state.1.pc,projection.1]
    · change s.gas.g-preparedExecWord64 (tr.cell 0 r) 502=preparedExecWord64 (tr.cell 0 (r+1)) 299
      rw [gas,state.1.gas]
  · right
    refine ⟨height,hh,?_,?_,?_⟩
    · rw [projection.2.2.2.1];exact present
    · intro i hi;rw [projection.2.2.2.2.1 i hi];exact heightSelected i hi
    · change f.labels=_
      rw [projection.2.2.2.2.2];exact labels

end NearCompression
