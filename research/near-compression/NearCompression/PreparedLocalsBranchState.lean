import NearCompression.PreparedLocalsUntaken
import NearCompression.PreparedLocalsBranchBounds
import NearCompression.PreparedLocalsControlDecode
import NearCompression.PreparedLocalsControlPreserve
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
theorem prepared_locals_setup_untaken_state (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedLocalsSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (branch : tr.cell 0 r 606=1) (zero : tr.cell 0 r 681=0)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedLocalsState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    0<sp ∧ ∃ s',step cfg eligible.setup.program s=.cont s' ∧
      PreparedLocalsState (tr.cell 0 (r+1)) s'
        {f with pc:=f.pc+1} fs (sp-1) count root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  have localH:=prepared_locals_exec_local codeCount count tr pub holds
  have preserve:=prepared_locals_control_array_preserved count state.2.1 tr 0 r pub localH nonlast 5 (by decide) branch
  have localsEq : f.locals=preparedLocalsArray (tr.cell 0 (r+1)) count:=state.2.2.trans preserve.symm
  obtain ⟨setup,func,checked⟩:=prepared_locals_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨op,code,charge,bound,_,ops,_,_⟩:=prepared_locals_control_decode codeCount count tr pub holds eligible.func _ checked r (by omega) 5 (by decide) branch
  have tag:=ops 5 (by decide)
  change tr.cell 0 r 606=(if 5=op.tag then 1 else 0) at tag
  rw [branch] at tag
  have opEq : op=PreparedControlInstruction.brIf := by
    cases op with
    | brIf => rfl
    | block => exact False.elim ((by decide : (1:Fp)≠0) tag)
    | legacy old => cases old <;> exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  rw [←state.1.1.pc] at code charge
  have enoughRow : preparedExecWord64 (tr.cell 0 r) 502≤preparedExecWord64 (tr.cell 0 r) 299 := by
    rw [←state.1.1.gas];exact enough
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr 0 r pub (prepared_locals_gas_source count) localH nonlast active enoughRow
  obtain ⟨sp',positive,spBound,selected,nextSelected,condition,words⟩:=
    prepared_locals_untaken_stack_projection count tr 0 r pub localH nonlast active charged branch zero
  have eq : sp'=sp := by
    have a:=selected sp' spBound
    have b:=state.1.1.selected sp' spBound
    rw [if_pos rfl] at a
    rw [a] at b
    by_cases eq:sp'=sp
    · exact eq
    · simp only [eq,ite_false] at b
      exact False.elim ((by decide : (1:Fp)≠0) b)
  subst sp'
  have projection:=prepared_locals_untaken_pc_label count tr 0 r pub localH nonlast active charged branch zero
  have labelOne:=(prepared_locals_branch_height count tr 0 r pub localH (by omega) active charged branch).1
  obtain ⟨height,hh,present,heightSelected,labels⟩ :
      ∃ height,height<9 ∧ tr.cell 0 r 639=1 ∧
        (∀ i,i<9 → tr.cell 0 r (640+i)=if i=height then 1 else 0) ∧
        f.labels=[{target:=preparedControlSavedTarget (tr.cell 0 r),arity:=0,height:=height,isLoop:=false},root] := by
    rcases state.1.2 with h|h
    · rw [labelOne] at h
      exact False.elim ((by decide : (1:Fp)≠0) h.1)
    · exact h
  let values:=preparedWasmStack (preparedExecGhostRow (tr.cell 0 r)) (sp-1)
  have stack : s.stack=values.push (.i32 0) := by
    rw [state.1.1.stack]
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
    state.1.1.frames (by rw [fn];exact func) code labels stack charge bound enough
  simp only [UInt32.toNat_zero,ite_true] at run
  let f' : Frame:={f with pc:=f.pc+1}
  let s' : St:={s with frames:=f'::fs,stack:=values,gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell 0 r) 502}}
  have run' : step cfg eligible.setup.program s=.cont s' := by
    simpa only [setFrame,state.1.1.frames] using run
  refine ⟨positive,s',run',⟨⟨?_,?_⟩,state.2.1,localsEq⟩,projection.2.1,projection.2.2.1⟩
  · refine ⟨by omega,nextSelected,rfl,?_,nextStack.symm,?_⟩
    · change f.pc+1=preparedCodeExecPC (tr.cell 0 (r+1))
      rw [state.1.1.pc,projection.1]
    · change s.gas.g-preparedExecWord64 (tr.cell 0 r) 502=preparedExecWord64 (tr.cell 0 (r+1)) 299
      rw [gas,state.1.1.gas]
  · right
    refine ⟨height,hh,?_,?_,?_⟩
    · rw [projection.2.2.2.1];exact present
    · intro i hi;rw [projection.2.2.2.2.1 i hi];exact heightSelected i hi
    · change f.labels=_
      rw [projection.2.2.2.2.2];exact labels

theorem prepared_locals_setup_taken_state (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedLocalsSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (branch : tr.cell 0 r 606=1) (nonzero : tr.cell 0 r 681=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedLocalsState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ height s',height<sp ∧ step cfg eligible.setup.program s=.cont s' ∧
      PreparedLocalsState (tr.cell 0 (r+1)) s'
        {f with pc:=preparedControlSavedTarget (tr.cell 0 r),labels:=[root]} fs height count root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  have localH:=prepared_locals_exec_local codeCount count tr pub holds
  have preserve:=prepared_locals_control_array_preserved count state.2.1 tr 0 r pub localH nonlast 5 (by decide) branch
  have localsEq : f.locals=preparedLocalsArray (tr.cell 0 (r+1)) count:=state.2.2.trans preserve.symm
  obtain ⟨setup,func,checked⟩:=prepared_locals_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨op,code,charge,bound,_,ops,_,_⟩:=prepared_locals_control_decode codeCount count tr pub holds eligible.func _ checked r (by omega) 5 (by decide) branch
  have tag:=ops 5 (by decide)
  change tr.cell 0 r 606=(if 5=op.tag then 1 else 0) at tag
  rw [branch] at tag
  have opEq : op=PreparedControlInstruction.brIf := by
    cases op with
    | brIf => rfl
    | block => exact False.elim ((by decide : (1:Fp)≠0) tag)
    | legacy old => cases old <;> exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  rw [←state.1.1.pc] at code charge
  have enoughRow : preparedExecWord64 (tr.cell 0 r) 502≤preparedExecWord64 (tr.cell 0 r) 299 := by
    rw [←state.1.1.gas];exact enough
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr 0 r pub (prepared_locals_gas_source count) localH nonlast active enoughRow
  have labelOne:=(prepared_locals_branch_height count tr 0 r pub localH (by omega) active charged branch).1
  obtain ⟨height,hh,present,heightSelected,labels⟩ :
      ∃ height,height<9 ∧ tr.cell 0 r 639=1 ∧
        (∀ i,i<9 → tr.cell 0 r (640+i)=if i=height then 1 else 0) ∧
        f.labels=[{target:=preparedControlSavedTarget (tr.cell 0 r),arity:=0,height:=height,isLoop:=false},root] := by
    rcases state.1.2 with h|h
    · rw [labelOne] at h
      exact False.elim ((by decide : (1:Fp)≠0) h.1)
    · exact h
  have below:=prepared_locals_branch_height_lt count tr 0 r pub localH (by omega) active charged branch sp height state.1.1.depth hh state.1.1.selected heightSelected
  have positive : 0<sp:=by omega
  obtain ⟨height',hh',saved',nextSelected⟩:=prepared_locals_taken_sp count tr 0 r pub localH nonlast active charged branch nonzero
  have heightEq : height'=height := by
    have a:=saved' height' hh'
    have b:=heightSelected height' hh'
    rw [if_pos rfl] at a
    rw [a] at b
    by_cases eq:height'=height
    · exact eq
    · simp only [eq,ite_false] at b
      exact False.elim ((by decide : (1:Fp)≠0) b)
  subst height'
  have words:=prepared_locals_taken_stack count tr 0 r pub localH nonlast active charged branch nonzero height hh heightSelected
  have condition:=prepared_control_condition_sound _ tr 0 r pub localH (by omega)
    (prepared_locals_condition_source count) sp state.1.1.depth positive state.1.1.selected
  have wordNonzero : preparedExecStackWord (tr.cell 0 r) (sp-1)≠0 := by
    intro z
    have flag:=condition.2.mpr z
    rw [nonzero] at flag
    exact (by decide : (1:Fp)≠0) flag
  have wordBound:=prepared_locals_stack_word_bound count tr 0 r pub localH (by omega) (sp-1) (by have h:=state.1.1.depth;omega)
  let conditionValue:=UInt32.ofNat (preparedExecStackWord (tr.cell 0 r) (sp-1))
  have conditionNonzero : conditionValue.toNat≠0 := by
    change (UInt32.ofNat _).toNat≠0
    rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt wordBound]
    exact wordNonzero
  let values:=preparedWasmStack (preparedExecGhostRow (tr.cell 0 r)) (sp-1)
  have stack : s.stack=values.push (.i32 conditionValue) := by
    rw [state.1.1.stack]
    conv => lhs;rw [show sp=(sp-1)+1 by omega]
    rfl
  have extracted : values.extract 0 height=preparedWasmStack (preparedExecGhostRow (tr.cell 0 r)) height :=
    prepared_control_stack_extract _ (sp-1) height (by omega)
  have nextStack : preparedWasmStack (preparedExecGhostRow (tr.cell 0 (r+1))) height=values.extract 0 height := by
    rw [extracted]
    apply prepared_wasm_stack_congr
    intro i hi
    have h:=words i (by omega)
    rw [if_pos hi] at h
    exact h
  have run:=prepared_control_step_br_if cfg eligible.setup.program s f fs eligible.func
    (preparedExecWord64 (tr.cell 0 r) 502) values conditionValue (preparedControlSavedTarget (tr.cell 0 r)) height root
    state.1.1.frames (by rw [fn];exact func) code labels stack charge bound enough
  simp only [conditionNonzero,ite_false] at run
  have pc:=prepared_locals_taken_pc count tr 0 r pub localH nonlast active charged branch nonzero
  have cleared:=prepared_locals_taken_label count tr 0 r pub localH nonlast active charged branch nonzero
  have endZero : tr.cell 0 r 469=0:=ops 3 (by decide)
  have status:=prepared_locals_continue_status count tr 0 r pub localH nonlast active charged (by rw [endZero];grind)
  let f' : Frame:={f with pc:=preparedControlSavedTarget (tr.cell 0 r),labels:=[root]}
  let s' : St:={s with frames:=f'::fs,stack:=values.extract 0 height,gas:={s.gas with g:=s.gas.g-preparedExecWord64 (tr.cell 0 r) 502}}
  have run' : step cfg eligible.setup.program s=.cont s' := by
    simpa only [setFrame,state.1.1.frames] using run
  refine ⟨height,s',below,run',⟨⟨?_,Or.inl ⟨cleared.1,rfl⟩⟩,state.2.1,localsEq⟩,status.2.1,status.2.2⟩
  refine ⟨hh,nextSelected,rfl,pc.symm,nextStack.symm,?_⟩
  change s.gas.g-preparedExecWord64 (tr.cell 0 r) 502=preparedExecWord64 (tr.cell 0 (r+1)) 299
  rw [gas,state.1.1.gas]

end NearCompression
