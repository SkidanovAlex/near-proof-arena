import NearCompression.PreparedExecStackClosure
import NearCompression.PreparedLiteralCertificates

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

theorem prepared_exec_authenticated_stack_exact (push : Bool)
    (ec cc boundary : List Expr) (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedCodeBusAir ec cc boundary count) pub tr)
    (codeSource : PreparedCodeOrderSource (preparedCodeDataTable cc))
    (inactive : ∀ i,i<25 → preparedCodeInactive (172+i)∈cc)
    (source : PreparedExecClosureSource (preparedCodeExecTable ec boundary))
    (gasSource : PreparedExecGasSource (preparedCodeExecTable ec boundary))
    (guard : PreparedExecHasSource (preparedCodeExecTable ec boundary) (preparedExecStackDepth push))
    (pf : PFunc) (fn : Nat) (checked : preparedCodeVariableCheck pf fn pub=true)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (isOp : tr.cell 0 r (466+(if push then 0 else 2))=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame) (sp : Nat)
    (state : PreparedExecState (tr.cell 0 r) s f fs sp)
    (func : p.funcs[f.fn]?=some pf)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    step cfg p s=.cont {s with
      stack:=preparedWasmStack (preparedExecGhostRow (tr.cell 0 (r+1))) (if push then sp+1 else sp-1)
      frames:={f with pc:=preparedCodeExecPC (tr.cell 0 (r+1))}::fs
      gas:={s.gas with g:=preparedExecWord64 (tr.cell 0 (r+1)) 299}} := by
  have localH:=prepared_exec_table_local ec cc boundary count tr pub holds
  have hr : r<tr.height 0:=by omega
  obtain ⟨op,code,immediate,ops⟩:=prepared_exec_authenticated_immediate ec cc boundary count tr pub holds
    codeSource inactive pf fn checked r hr
  have wantedBound : (if push then 0 else 2)<4 := by cases push <;> decide
  have tag:=ops (if push then 0 else 2) wantedBound
  rw [isOp] at tag
  have tagEq : op.tag=(if push then 0 else 2) := by
    by_cases eq:(if push then 0 else 2)=op.tag
    · exact eq.symm
    · simp only [eq,ite_false] at tag
      exact False.elim ((by decide : (1:Fp)≠0) tag)
  have opBits : ∀ i,i<4 → tr.cell 0 r (466+i)=if i=(if push then 0 else 2) then 1 else 0 := by
    simpa only [tagEq] using ops
  have actualCode : pf.code[f.pc]?=some (if push then .i32Const
      (UInt32.ofNat (preparedExecImmediate (tr.cell 0 r))) else .drop) := by
    rw [state.pc,immediate]
    cases push <;> cases op <;>
      simp only [PreparedPublicInstruction.tag,Bool.false_eq_true,ite_true,ite_false] at tagEq ⊢
    all_goals try simp only [Nat.reduceEqDiff] at tagEq
    all_goals simpa [PreparedPublicInstruction.instr,PreparedPublicInstruction.immediate] using code
  obtain ⟨_,charge,bounded⟩:=prepared_exec_authenticated_fee ec cc boundary count tr pub holds
    codeSource inactive pf fn checked r hr
  have enoughRow : preparedExecWord64 (tr.cell 0 r) 502≤preparedExecWord64 (tr.cell 0 r) 299 := by
    rw [←state.gas];exact enough
  obtain ⟨noBorrow,gasNext⟩:=prepared_exec_gas_success _ tr 0 r pub gasSource localH nonlast active enoughRow
  obtain ⟨_,height,hot⟩:=prepared_exec_stack_next_sp push _ tr 0 r pub localH nonlast source active noBorrow
    opBits sp state.depth state.selected
  have endZero:=opBits 3 (by decide)
  have notThree : ¬3=(if push then 0 else 2):=by cases push <;> decide
  simp only [notThree,ite_false] at endZero
  have flags:=prepared_exec_success_flags _ tr 0 r pub localH nonlast source active noBorrow endZero
  have adv : preparedExecPCAdvance.eval tr 0 r pub=Fp.ofNat 1 := by
    change (((1:Fp)+ -tr.cell 0 r 41)*((1:Fp)+ -tr.cell 0 r 430))*((1:Fp)+ -tr.cell 0 r 469)=1
    rw [active,noBorrow,endZero];grind
  have pcNext:=prepared_exec_pc_transition _ tr 0 pub gasSource.pc localH r nonlast 1 (by decide) adv
  have run:=prepared_exec_table_wasm_stack push _ tr 0 r pub localH nonlast source.localSource guard active noBorrow
    opBits cfg p s f fs pf sp (preparedExecWord64 (tr.cell 0 r) 502) state.depth state.selected
    state.frames state.stack func actualCode (by rw [state.pc];exact charge) bounded enough
  rw [prepared_exec_next_stack] at run
  simp only [pcNext,gasNext,←state.pc,←state.gas]
  exact run

/-- Exact fast-gas update plus real continuation preserves the no-host gas
context; the changed frame/stack do not affect this invariant. -/
theorem prepared_exec_continue_context (cfg : NearCfg) (p : Prepared) (s next : St)
    (stack : Array Val) (frames : List Frame) (gas : Nat)
    (run : step cfg p s=.cont next)
    (exactStep : step cfg p s=.cont {s with stack:=stack,frames:=frames,gas:={s.gas with g:=gas}})
    (context : PreparedWasmGasContext s) (decreases : gas≤s.gas.g) : PreparedWasmGasContext next := by
  have eq : next={s with stack:=stack,frames:=frames,gas:={s.gas with g:=gas}} :=
    Res.cont.inj (run.symm.trans exactStep)
  subst next
  rcases context with ⟨a,b,c,d,e⟩
  exact ⟨a,b,c,by change gas≤s.gas.prepaid-s.gas.burnt;omega,e⟩

/-- Literal-table continuation with preserved actual gas context, ready for
induction over successive execution rows. -/
theorem prepared_literal_continue (op : Option Bool) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedLiteralAir count) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedCodeVariableCheck pf fn pub=true)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (isOp : tr.cell 0 r (466+preparedWasmOpTag op)=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame) (sp : Nat)
    (state : PreparedExecState (tr.cell 0 r) s f fs sp)
    (func : p.funcs[f.fn]?=some pf) (context : PreparedWasmGasContext s)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ s',step cfg p s=.cont s' ∧
      PreparedExecState (tr.cell 0 (r+1)) s'
        {f with pc:=preparedCodeExecPC (tr.cell 0 (r+1))} fs (preparedWasmNextSP op sp) ∧
      PreparedWasmGasContext s' ∧ tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  have localH:=prepared_exec_table_local _ _ _ count tr pub holds
  have enoughRow : preparedExecWord64 (tr.cell 0 r) 502≤preparedExecWord64 (tr.cell 0 r) 299 := by
    rw [←state.gas];exact enough
  have gasNext:=(prepared_exec_gas_success _ tr 0 r pub prepared_literal_exec_gas localH nonlast active enoughRow).2
  have decreases : preparedExecWord64 (tr.cell 0 (r+1)) 299≤s.gas.g := by
    rw [gasNext,←state.gas];omega
  have assemble (nsp : Nat)
      (closed : ∃ s',step cfg p s=.cont s' ∧
        PreparedExecState (tr.cell 0 (r+1)) s' {f with pc:=preparedCodeExecPC (tr.cell 0 (r+1))} fs nsp ∧
        tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0)
      (exactStep : step cfg p s=.cont {s with
        stack:=preparedWasmStack (preparedExecGhostRow (tr.cell 0 (r+1))) nsp
        frames:={f with pc:=preparedCodeExecPC (tr.cell 0 (r+1))}::fs
        gas:={s.gas with g:=preparedExecWord64 (tr.cell 0 (r+1)) 299}}) :
      ∃ s',step cfg p s=.cont s' ∧
        PreparedExecState (tr.cell 0 (r+1)) s' {f with pc:=preparedCodeExecPC (tr.cell 0 (r+1))} fs nsp ∧
        PreparedWasmGasContext s' ∧ tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
    obtain ⟨next,run,post,flags⟩:=closed
    exact ⟨next,run,post,prepared_exec_continue_context cfg p s next _ _ _ run exactStep context decreases,flags⟩
  cases op with
  | none =>
    apply assemble (sp-1)
    · exact prepared_exec_authenticated_add_closed _ _ _ count tr pub holds prepared_literal_code_order
        prepared_literal_code_inactive prepared_literal_exec_closure prepared_literal_exec_gas
        pf fn checked r nonlast active isOp cfg p s f fs sp state func enough
    · have run:=prepared_exec_authenticated_add _ _ _ count tr pub holds prepared_literal_code_order
        prepared_literal_code_inactive prepared_literal_exec_local prepared_literal_exec_gas
        pf fn checked r nonlast active isOp cfg p s f fs sp state func enough
      rw [prepared_exec_next_stack] at run
      exact run
  | some push =>
    have nextEq : preparedWasmNextSP (some push) sp=(if push then sp+1 else sp-1) := by cases push <;> rfl
    have tagEq : preparedWasmOpTag (some push)=(if push then 0 else 2) := by cases push <;> rfl
    rw [nextEq]
    rw [tagEq] at isOp
    apply assemble (if push then sp+1 else sp-1)
    · exact prepared_exec_authenticated_stack_closed push _ _ _ count tr pub holds prepared_literal_code_order
        prepared_literal_code_inactive prepared_literal_exec_closure prepared_literal_exec_gas
        (prepared_literal_exec_stack_guard push) pf fn checked r nonlast active isOp
        cfg p s f fs sp state func enough
    · exact prepared_exec_authenticated_stack_exact push _ _ _ count tr pub holds prepared_literal_code_order
        prepared_literal_code_inactive prepared_literal_exec_closure prepared_literal_exec_gas
        (prepared_literal_exec_stack_guard push) pf fn checked r nonlast active isOp
        cfg p s f fs sp state func enough

end NearCompression
