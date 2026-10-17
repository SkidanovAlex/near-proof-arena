import NearCompression.PreparedExecClosure
import NearCompression.PreparedExecStack

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

theorem prepared_exec_stack_next_sp (push : Bool) (table : Table) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal table tr t pub) (nonlast : r+1<tr.height t) (source : PreparedExecClosureSource table)
    (active : tr.cell t r 41=0) (noBorrow : tr.cell t r 430=0)
    (op : ∀ i,i<4 → tr.cell t r (466+i)=if i=(if push then 0 else 2) then 1 else 0)
    (sp : Nat) (hs : sp<9) (selected : ∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    (if push then sp<8 else 1≤sp) ∧ (if push then sp+1 else sp-1)<9 ∧
    ∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=(if push then sp+1 else sp-1) then 1 else 0 := by
  have projection:=prepared_exec_table_projection table tr t r pub localH nonlast source.localSource
  obtain ⟨nsp,hn,hot⟩:=prepared_exec_sp_onehot table tr t (r+1) pub localH nonlast source
  have opOld:=prepared_exec_opcode_projection (tr.cell t r) (tr.cell t (r+1))
    (fun i=>pub.getD i 0) (if push then 0 else 2) op
  have success : preparedSuccessExpr.evalWith (preparedRowEnv (preparedExecGhostRow (tr.cell t r))
      (preparedExecGhostNext (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0))
      (preparedExecGhostPub (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0)) 0 0)=1 := by
    change ((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430)=1
    rw [active,noBorrow];grind
  have current : ∀ i,i<9 → preparedExecGhostRow (tr.cell t r) (16+i)=if i=sp then 1 else 0 := by
    intro i hi
    simpa [preparedExecGhostRow,show ¬16+i<16 by omega,show ¬i+16<16 by omega,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using selected i hi
  have following : ∀ i,i<9 → preparedExecGhostNext (tr.cell t r) (tr.cell t (r+1))
      (fun i=>pub.getD i 0) (16+i)=if i=nsp then 1 else 0 := by
    intro i hi
    rw [prepared_exec_ghost_next_column _ _ _ _ (by omega)]
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hot i hi
  have eq:=prepared_stack_pointer_next push _ _ _ projection.2 success opOld sp nsp hs hn current following
  cases push <;> simp only [Bool.false_eq_true,ite_true,ite_false,Nat.add_zero] at eq ⊢
  · have ns:nsp=sp-1:=by omega
    exact ⟨by omega,by omega,by simpa only [ns] using hot⟩
  · exact ⟨by omega,by omega,by simpa only [eq] using hot⟩

/-- Authenticated const/drop preserves the full real-state relation at the
next row. Both instruction/immediate and range fee come from checked prepare
metadata through natural CODE-bus authentication. -/
theorem prepared_exec_authenticated_stack_closed (push : Bool)
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
    ∃ s',step cfg p s=.cont s' ∧
      PreparedExecState (tr.cell 0 (r+1)) s'
        {f with pc:=preparedCodeExecPC (tr.cell 0 (r+1))} fs (if push then sp+1 else sp-1) ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
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
  let result : St := {s with
    stack:=preparedWasmStack (preparedExecGhostRow (tr.cell 0 (r+1))) (if push then sp+1 else sp-1)
    frames:={f with pc:=preparedCodeExecPC (tr.cell 0 (r+1))}::fs
    gas:={s.gas with g:=preparedExecWord64 (tr.cell 0 (r+1)) 299}}
  refine ⟨result,?_,?_,flags.2.1,flags.2.2⟩
  · simp only [result,pcNext,gasNext,←state.pc,←state.gas]
    exact run
  · exact ⟨height,hot,rfl,rfl,rfl,rfl⟩

end NearCompression
