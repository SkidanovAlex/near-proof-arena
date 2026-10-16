import NearCompression.PreparedLocalsControlDecode
import NearCompression.PreparedLocalsLegacyLocal
import NearCompression.PreparedLocalsSequential
import NearCompression.PreparedLocalsFrameWrite
import NearCompression.PreparedControlLegacyState
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
theorem prepared_locals_setup_add_state (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedLocalsSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0) (isAdd : tr.cell 0 r 467=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedLocalsState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ s',step cfg eligible.setup.program s=.cont s' ∧
      PreparedLocalsState (tr.cell 0 (r+1)) s' {f with pc:=f.pc+1} fs (sp-1) count root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  have localH:=prepared_locals_exec_local codeCount count tr pub holds
  obtain ⟨setup,func,checked⟩:=prepared_locals_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨op,code,charge,bound,immediate,ops,localsZero,_⟩:=prepared_locals_control_decode codeCount count tr pub holds eligible.func _ checked r (by omega) 1 (by decide) isAdd
  have tag:=ops 1 (by decide)
  change tr.cell 0 r 467=(if 1=op.tag then 1 else 0) at tag
  rw [isAdd] at tag
  have opEq : op=PreparedControlInstruction.legacy .add := by
    cases op with
    | block => exact False.elim ((by decide : (1:Fp)≠0) tag)
    | brIf => exact False.elim ((by decide : (1:Fp)≠0) tag)
    | legacy old => cases old <;> first | rfl | exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  rw [←state.1.1.pc] at code charge
  have oldOps : ∀ i,i<4 → tr.cell 0 r (466+i)=if i=1 then 1 else 0 := by
    intro i hi
    have h:=ops i (by omega)
    change tr.cell 0 r (if i<4 then 466+i else 605+(i-4))=(if i=1 then 1 else 0) at h
    rw [if_pos hi] at h
    exact h
  have br : tr.cell 0 r 606=0:=ops 5 (by decide)
  have bl : tr.cell 0 r 605=0:=ops 4 (by decide)
  have en : tr.cell 0 r 469=0:=ops 3 (by decide)
  have enoughRow : preparedExecWord64 (tr.cell 0 r) 502≤preparedExecWord64 (tr.cell 0 r) 299 := by rw [←state.1.1.gas];exact enough
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr 0 r pub (prepared_locals_gas_source count) localH nonlast active enoughRow
  have zeros : ∀c,c=606 ∨ c=683 ∨ c=684 ∨ c=685 → tr.cell 0 r c=0 := by
    intro c hc
    rcases hc with eq|eq|eq|eq <;> subst c
    · exact br
    · exact localsZero 0 (by decide)
    · exact localsZero 1 (by decide)
    · exact localsZero 2 (by decide)
  have preserve:=prepared_locals_array_preserved count state.2.1 tr 0 r pub localH nonlast (by
    intro slot hs
    change preparedLocalsSuccess.eval tr 0 r pub*((tr.cell 0 r 684+tr.cell 0 r 685)*tr.cell 0 r (814+slot))=0
    rw [localsZero 1 (by decide),localsZero 2 (by decide)];grind)
  have projection:=prepared_locals_pc_label count tr 0 r pub localH nonlast active charged en bl br
  obtain ⟨_,depth,nextSelected⟩:=prepared_locals_legacy_add_next_sp count tr 0 r pub localH nonlast zeros active charged oldOps sp state.1.1.depth state.1.1.selected
  have run:=prepared_locals_legacy_wasm_add count tr 0 r pub localH nonlast zeros active charged oldOps
    cfg eligible.setup.program s f fs eligible.func sp (preparedExecWord64 (tr.cell 0 r) 502) state.1.1.depth
    state.1.1.selected state.1.1.frames state.1.1.stack (by rw [fn];exact func) code charge bound enough
  rw [prepared_exec_next_stack] at run
  refine ⟨_,run,⟨⟨?_,?_⟩,state.2.1,?_⟩,projection.2.1,projection.2.2.1⟩
  · refine ⟨depth,nextSelected,rfl,?_,rfl,?_⟩
    · change f.pc+1=preparedCodeExecPC (tr.cell 0 (r+1))
      rw [state.1.1.pc,projection.1]
    · change s.gas.g-preparedExecWord64 (tr.cell 0 r) 502=preparedExecWord64 (tr.cell 0 (r+1)) 299
      rw [gas,state.1.1.gas]
  · exact prepared_control_labels_transport _ _ _ _ root state.1.2 rfl
      projection.2.2.2.1 projection.2.2.2.2.1 projection.2.2.2.2.2
  · change f.locals=preparedLocalsArray (tr.cell 0 (r+1)) count
    rw [preserve,state.2.2]

theorem prepared_locals_setup_stack_state (push : Bool) (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedLocalsSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (isOp : tr.cell 0 r (466+(if push then 0 else 2))=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedLocalsState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ s',step cfg eligible.setup.program s=.cont s' ∧
      PreparedLocalsState (tr.cell 0 (r+1)) s' {f with pc:=f.pc+1} fs (if push then sp+1 else sp-1) count root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  have localH:=prepared_locals_exec_local codeCount count tr pub holds
  obtain ⟨setup,func,checked⟩:=prepared_locals_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨op,code,charge,bound,immediate,ops,localsZero,_⟩:=prepared_locals_control_decode codeCount count tr pub holds eligible.func _ checked r (by omega) (if push then 0 else 2) (by cases push <;> decide) (by simpa only [preparedControlOpcodeColumn,show (if push then 0 else 2)<4 by cases push <;> decide,ite_true] using isOp)
  have wantedBound : (if push then 0 else 2)<4 := by cases push <;> decide
  have tag:=ops (if push then 0 else 2) (by omega)
  change tr.cell 0 r (preparedControlOpcodeColumn (if push then 0 else 2))=(if (if push then 0 else 2)=op.tag then 1 else 0) at tag
  simp only [preparedControlOpcodeColumn,wantedBound,ite_true] at tag
  rw [isOp] at tag
  have tagEq : op.tag=(if push then 0 else 2) := by
    by_cases eq:(if push then 0 else 2)=op.tag
    · exact eq.symm
    · simp only [eq,ite_false] at tag
      exact False.elim ((by decide : (1:Fp)≠0) tag)
  have oldOps : ∀ i,i<4 → tr.cell 0 r (466+i)=if i=(if push then 0 else 2) then 1 else 0 := by
    intro i hi
    have h:=ops i (by omega)
    change tr.cell 0 r (if i<4 then 466+i else 605+(i-4))=(if i=op.tag then 1 else 0) at h
    rw [if_pos hi,tagEq] at h
    exact h
  have br : tr.cell 0 r 606=0 := by
    have h:=ops 5 (by decide)
    change tr.cell 0 r 606=(if 5=op.tag then 1 else 0) at h
    rw [tagEq,if_neg (by cases push <;> decide)] at h;exact h
  have bl : tr.cell 0 r 605=0 := by
    have h:=ops 4 (by decide)
    change tr.cell 0 r 605=(if 4=op.tag then 1 else 0) at h
    rw [tagEq,if_neg (by cases push <;> decide)] at h;exact h
  have en : tr.cell 0 r 469=0 := by
    have h:=oldOps 3 (by decide)
    rw [if_neg (by cases push <;> decide)] at h;exact h
  have actualCode : eligible.func.code[f.pc]?=some (if push then .i32Const
      (UInt32.ofNat (preparedExecImmediate (tr.cell 0 r))) else .drop) := by
    rw [state.1.1.pc,immediate]
    cases push <;> cases op with
    | block | brIf => simp [PreparedControlInstruction.tag] at tagEq
    | legacy old =>
      cases old <;> simp only [PreparedControlInstruction.tag,PreparedPublicInstruction.tag,Bool.false_eq_true,ite_true,ite_false] at tagEq ⊢
      all_goals try simp only [Nat.reduceEqDiff] at tagEq
      all_goals simpa [PreparedControlInstruction.instr,PreparedControlInstruction.immediate,PreparedPublicInstruction.instr,PreparedPublicInstruction.immediate] using code
  rw [←state.1.1.pc] at charge
  have enoughRow : preparedExecWord64 (tr.cell 0 r) 502≤preparedExecWord64 (tr.cell 0 r) 299 := by rw [←state.1.1.gas];exact enough
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr 0 r pub (prepared_locals_gas_source count) localH nonlast active enoughRow
  have zeros : ∀c,c=606 ∨ c=683 ∨ c=684 ∨ c=685 → tr.cell 0 r c=0 := by
    intro c hc
    rcases hc with eq|eq|eq|eq <;> subst c
    · exact br
    · exact localsZero 0 (by decide)
    · exact localsZero 1 (by decide)
    · exact localsZero 2 (by decide)
  have preserve:=prepared_locals_array_preserved count state.2.1 tr 0 r pub localH nonlast (by
    intro slot hs
    change preparedLocalsSuccess.eval tr 0 r pub*((tr.cell 0 r 684+tr.cell 0 r 685)*tr.cell 0 r (814+slot))=0
    rw [localsZero 1 (by decide),localsZero 2 (by decide)];grind)
  have projection:=prepared_locals_pc_label count tr 0 r pub localH nonlast active charged en bl br
  obtain ⟨_,depth,nextSelected⟩:=prepared_locals_legacy_stack_next_sp push count tr 0 r pub localH nonlast zeros active charged oldOps sp state.1.1.depth state.1.1.selected
  have run:=prepared_locals_legacy_wasm_stack push count tr 0 r pub localH nonlast zeros active charged oldOps
    cfg eligible.setup.program s f fs eligible.func sp (preparedExecWord64 (tr.cell 0 r) 502) state.1.1.depth
    state.1.1.selected state.1.1.frames state.1.1.stack (by rw [fn];exact func) actualCode charge bound enough
  rw [prepared_exec_next_stack] at run
  refine ⟨_,run,⟨⟨?_,?_⟩,state.2.1,?_⟩,projection.2.1,projection.2.2.1⟩
  · refine ⟨depth,nextSelected,rfl,?_,rfl,?_⟩
    · change f.pc+1=preparedCodeExecPC (tr.cell 0 (r+1))
      rw [state.1.1.pc,projection.1]
    · change s.gas.g-preparedExecWord64 (tr.cell 0 r) 502=preparedExecWord64 (tr.cell 0 (r+1)) 299
      rw [gas,state.1.1.gas]
  · exact prepared_control_labels_transport _ _ _ _ root state.1.2 rfl
      projection.2.2.2.1 projection.2.2.2.2.1 projection.2.2.2.2.2
  · change f.locals=preparedLocalsArray (tr.cell 0 (r+1)) count
    rw [preserve,state.2.2]

end NearCompression
