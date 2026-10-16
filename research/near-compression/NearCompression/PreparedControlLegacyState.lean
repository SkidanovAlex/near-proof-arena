import NearCompression.PreparedControlLegacyLocal
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

theorem prepared_control_labels_transport (row next : Nat → Fp) (f f' : Frame) (root : Label)
    (state : PreparedControlLabels row f root) (labels : f'.labels=f.labels)
    (flag : next 639=row 639) (heights : ∀ i,i<9 → next (640+i)=row (640+i))
    (target : preparedControlSavedTarget next=preparedControlSavedTarget row) :
    PreparedControlLabels next f' root := by
  rcases state with ⟨zero,rootOnly⟩|⟨height,bound,one,selected,frames⟩
  · exact Or.inl ⟨flag.trans zero,labels.trans rootOnly⟩
  · right
    refine ⟨height,bound,flag.trans one,?_,?_⟩
    · intro i hi;rw [heights i hi];exact selected i hi
    · rw [labels,target];exact frames

/-- Ordinary add on the control table: real prepared bytes and CODE balance
supply the instruction/fee; conditional source equations supply both operands
and all stack writes. Nested labels are retained. -/
theorem prepared_control_setup_add_state (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedControlSetupCheck cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0) (isAdd : tr.cell 0 r 467=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedControlState (tr.cell 0 r) s f fs sp root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ s',step cfg eligible.setup.program s=.cont s' ∧
      PreparedControlState (tr.cell 0 (r+1)) s' {f with pc:=f.pc+1} fs (sp-1) root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  have localH:=prepared_control_exec_local count tr pub holds
  obtain ⟨setup,func,checked⟩:=prepared_control_setup_checked cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨_,op,code,charge,bound,ops,_⟩:=prepared_control_authenticated_decode count tr pub holds eligible.func _ checked r (by omega)
  have tag:=ops 1 (by decide)
  change tr.cell 0 r 467=(if 1=op.tag then 1 else 0) at tag
  rw [isAdd] at tag
  have opEq : op=PreparedControlInstruction.legacy .add := by
    cases op with
    | block => exact False.elim ((by decide : (1:Fp)≠0) tag)
    | brIf => exact False.elim ((by decide : (1:Fp)≠0) tag)
    | legacy old => cases old <;> first | rfl | exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  rw [←state.1.pc] at code charge
  have oldOps : ∀ i,i<4 → tr.cell 0 r (466+i)=if i=1 then 1 else 0 := by
    intro i hi
    have h:=ops i (by omega)
    change tr.cell 0 r (if i<4 then 466+i else 605+(i-4))=(if i=1 then 1 else 0) at h
    rw [if_pos hi] at h
    exact h
  have br : tr.cell 0 r 606=0:=ops 5 (by decide)
  have bl : tr.cell 0 r 605=0:=ops 4 (by decide)
  have en : tr.cell 0 r 469=0:=ops 3 (by decide)
  have enoughRow : preparedExecWord64 (tr.cell 0 r) 502≤preparedExecWord64 (tr.cell 0 r) 299 := by rw [←state.1.gas];exact enough
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr 0 r pub prepared_control_literal_gas_source localH nonlast active enoughRow
  have projection:=prepared_control_legacy_pc_label tr 0 r pub localH nonlast active charged br bl en
  obtain ⟨_,depth,nextSelected⟩:=prepared_control_legacy_add_next_sp tr 0 r pub localH nonlast br active charged oldOps sp state.1.depth state.1.selected
  have run:=prepared_control_legacy_wasm_add tr 0 r pub localH nonlast br active charged oldOps
    cfg eligible.setup.program s f fs eligible.func sp (preparedExecWord64 (tr.cell 0 r) 502) state.1.depth
    state.1.selected state.1.frames state.1.stack (by rw [fn];exact func) code charge bound enough
  rw [prepared_exec_next_stack] at run
  refine ⟨_,run,⟨?_,?_⟩,projection.2.1,projection.2.2.1⟩
  · refine ⟨depth,nextSelected,rfl,?_,rfl,?_⟩
    · change f.pc+1=preparedCodeExecPC (tr.cell 0 (r+1))
      rw [state.1.pc,projection.1]
    · change s.gas.g-preparedExecWord64 (tr.cell 0 r) 502=preparedExecWord64 (tr.cell 0 (r+1)) 299
      rw [gas,state.1.gas]
  · exact prepared_control_labels_transport _ _ _ _ root state.2 rfl
      projection.2.2.2.1 projection.2.2.2.2.1 projection.2.2.2.2.2

theorem prepared_control_authenticated_immediate (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedControlCodeCheck pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) :
    ∃ op:PreparedControlInstruction,pf.code[preparedCodeExecPC (tr.cell 0 r)]?=some op.instr ∧
      preparedExecImmediate (tr.cell 0 r)=op.immediate ∧
      ∀ i,i<6 → tr.cell 0 r (preparedControlOpcodeColumn i)=if i=op.tag then 1 else 0 := by
  obtain ⟨_,op,fee,amount,target,code,_,_,_,_,_,fields⟩:=
    prepared_control_authenticated_fetch count tr pub holds pf fn checked r hr
  refine ⟨op,code,?_,?_⟩
  · have lo:=fields 8 (by decide)
    have hi:=fields 9 (by decide)
    change (preparedCodeBits 470).eval tr 0 r pub=Fp.ofNat ((op.immediate/65536^0)%65536) at lo
    change (preparedCodeBits 486).eval tr 0 r pub=Fp.ofNat ((op.immediate/65536^1)%65536) at hi
    rw [prepared_code_bits_eval] at lo hi
    simp only [Bool.false_eq_true,ite_false] at lo hi
    unfold preparedExecImmediate
    rw [lo,hi,prepared_code_digit_nat,prepared_code_digit_nat]
    simp only [Nat.reducePow,Nat.div_one]
    apply prepared_code_digits32
    cases op with
    | legacy old => cases old with
      | constant v => exact v.toNat_lt
      | _ => decide
    | _ => decide
  · intro i hi
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5:=by omega
    rcases cases with z|z|z|z|z|z <;> subst i
    · exact fields 4 (by decide)
    · exact fields 5 (by decide)
    · exact fields 6 (by decide)
    · exact fields 7 (by decide)
    · exact fields 25 (by decide)
    · exact fields 26 (by decide)

/-- Prepared const/drop successor state, including authenticated immediate,
exact gas and live-stack writes, with the current control label retained. -/
theorem prepared_control_setup_stack_state (push : Bool) (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedControlSetupCheck cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (isOp : tr.cell 0 r (466+(if push then 0 else 2))=1)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedControlState (tr.cell 0 r) s f fs sp root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ s',step cfg eligible.setup.program s=.cont s' ∧
      PreparedControlState (tr.cell 0 (r+1)) s' {f with pc:=f.pc+1} fs (if push then sp+1 else sp-1) root ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  have localH:=prepared_control_exec_local count tr pub holds
  obtain ⟨setup,func,checked⟩:=prepared_control_setup_checked cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨op,code,immediate,ops⟩:=prepared_control_authenticated_immediate count tr pub holds eligible.func _ checked r (by omega)
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
    rw [state.1.pc,immediate]
    cases push <;> cases op with
    | block | brIf => simp [PreparedControlInstruction.tag] at tagEq
    | legacy old =>
      cases old <;> simp only [PreparedControlInstruction.tag,PreparedPublicInstruction.tag,Bool.false_eq_true,ite_true,ite_false] at tagEq ⊢
      all_goals try simp only [Nat.reduceEqDiff] at tagEq
      all_goals simpa [PreparedControlInstruction.instr,PreparedControlInstruction.immediate,PreparedPublicInstruction.instr,PreparedPublicInstruction.immediate] using code
  obtain ⟨_,_,_,charge,bound,_,_⟩:=prepared_control_authenticated_decode count tr pub holds eligible.func _ checked r (by omega)
  rw [←state.1.pc] at charge
  have enoughRow : preparedExecWord64 (tr.cell 0 r) 502≤preparedExecWord64 (tr.cell 0 r) 299 := by rw [←state.1.gas];exact enough
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr 0 r pub prepared_control_literal_gas_source localH nonlast active enoughRow
  have projection:=prepared_control_legacy_pc_label tr 0 r pub localH nonlast active charged br bl en
  obtain ⟨_,depth,nextSelected⟩:=prepared_control_legacy_stack_next_sp push tr 0 r pub localH nonlast br active charged oldOps sp state.1.depth state.1.selected
  have run:=prepared_control_legacy_wasm_stack push tr 0 r pub localH nonlast br active charged oldOps
    cfg eligible.setup.program s f fs eligible.func sp (preparedExecWord64 (tr.cell 0 r) 502) state.1.depth
    state.1.selected state.1.frames state.1.stack (by rw [fn];exact func) actualCode charge bound enough
  rw [prepared_exec_next_stack] at run
  refine ⟨_,run,⟨?_,?_⟩,projection.2.1,projection.2.2.1⟩
  · refine ⟨depth,nextSelected,rfl,?_,rfl,?_⟩
    · change f.pc+1=preparedCodeExecPC (tr.cell 0 (r+1))
      rw [state.1.pc,projection.1]
    · change s.gas.g-preparedExecWord64 (tr.cell 0 r) 502=preparedExecWord64 (tr.cell 0 (r+1)) 299
      rw [gas,state.1.gas]
  · exact prepared_control_labels_transport _ _ _ _ root state.2 rfl
      projection.2.2.2.1 projection.2.2.2.2.1 projection.2.2.2.2.2

end NearCompression
