import NearCompression.PreparedExecClosure
import NearCompression.PreparedWasmTerminal

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

theorem prepared_exec_terminal_flags (table : Table) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal table tr t pub) (nonlast : r+1<tr.height t) (source : PreparedExecClosureSource table)
    (active : tr.cell t r 41=0) :
    tr.cell t r 42=0 ∧ tr.cell t (r+1) 42=tr.cell t r 430 ∧
    tr.cell t (r+1) 41=tr.cell t r 430+
      ((1-tr.cell t r 41)*(1-tr.cell t r 430))*tr.cell t r 469 := by
  have result:=prepared_terminal_flags_local
    (preparedExecGhostRow (tr.cell t r))
    (preparedExecGhostNext (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0))
    (preparedExecGhostPub (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0))
    active
    ((prepared_exec_lower_eval _ _ _ _).symm.trans
      (prepared_exec_source_eval table tr t r pub localH nonlast _ source.invariant))
    ((prepared_exec_lower_eval _ _ _ _).symm.trans
      (prepared_exec_source_eval table tr t r pub localH nonlast _ source.done))
    ((prepared_exec_lower_eval _ _ _ _).symm.trans
      (prepared_exec_source_eval table tr t r pub localH nonlast _ source.failed))
  rw [←prepared_exec_lower_eval (preparedFetchPython 3)] at result
  change tr.cell t r 42=0 ∧ tr.cell t (r+1) 42=tr.cell t r 430 ∧
    tr.cell t (r+1) 41=tr.cell t r 430+
      (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*tr.cell t r 469 at result
  grind

/-- Exact actual trap and interpreter failure gas, plus AIR terminal flags.
The fast-gas snapshot freezes, while actual burnt gas follows synchronization
and failure burning; these are deliberately distinct representations. -/
theorem prepared_exec_authenticated_exhaustion (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedCodeBusAir ec cc boundary count) pub tr)
    (codeSource : PreparedCodeOrderSource (preparedCodeDataTable cc))
    (inactive : ∀ i,i<25 → preparedCodeInactive (172+i)∈cc)
    (source : PreparedExecClosureSource (preparedCodeExecTable ec boundary))
    (gasSource : PreparedExecGasSource (preparedCodeExecTable ec boundary))
    (pf : PFunc) (fn : Nat) (checked : preparedCodeVariableCheck pf fn pub=true)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame) (sp : Nat)
    (state : PreparedExecState (tr.cell 0 r) s f fs sp)
    (func : p.funcs[f.fn]?=some pf) (context : PreparedWasmGasContext s)
    (insufficient : s.gas.g<preparedExecWord64 (tr.cell 0 r) 502) :
    step cfg p s=.abort {s with gas:=preparedWasmFailureGas s (preparedExecWord64 (tr.cell 0 r) 502)}
      (preparedWasmFailureError s (preparedExecWord64 (tr.cell 0 r) 502)) ∧
    tr.cell 0 (r+1) 41=1 ∧ tr.cell 0 (r+1) 42=1 ∧
    preparedExecWord64 (tr.cell 0 (r+1)) 299=s.gas.g := by
  have localH:=prepared_exec_table_local ec cc boundary count tr pub holds
  have hr : r<tr.height 0:=by omega
  obtain ⟨op,code,_⟩:=prepared_exec_authenticated_opcode ec cc boundary count tr pub holds
    codeSource inactive pf fn checked r hr
  obtain ⟨_,charge,bounded⟩:=prepared_exec_authenticated_fee ec cc boundary count tr pub holds
    codeSource inactive pf fn checked r hr
  have insufficientRow : preparedExecWord64 (tr.cell 0 r) 299<preparedExecWord64 (tr.cell 0 r) 502 := by
    rw [←state.gas];exact insufficient
  obtain ⟨borrow,frozen⟩:=prepared_exec_gas_exhaustion _ tr 0 r pub gasSource localH nonlast insufficientRow
  have flags:=prepared_exec_terminal_flags _ tr 0 r pub localH nonlast source active
  have run:=prepared_wasm_exhaustion_trap cfg p s f fs pf op.instr (preparedExecWord64 (tr.cell 0 r) 502)
    state.frames func (by rw [state.pc];exact code) (by rw [state.pc];exact charge) bounded insufficient context
  refine ⟨run,?_,?_,?_⟩
  · rw [borrow] at flags
    grind
  · exact flags.2.1.trans borrow
  · exact frozen.trans state.gas.symm

/-- Successful final-frame end: the source end-depth guard proves empty live
stack; authenticated CODE and fee determine the actual return and gas update. -/
theorem prepared_exec_authenticated_end (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedCodeBusAir ec cc boundary count) pub tr)
    (codeSource : PreparedCodeOrderSource (preparedCodeDataTable cc))
    (inactive : ∀ i,i<25 → preparedCodeInactive (172+i)∈cc)
    (source : PreparedExecClosureSource (preparedCodeExecTable ec boundary))
    (gasSource : PreparedExecGasSource (preparedCodeExecTable ec boundary))
    (guard : PreparedExecHasSource (preparedCodeExecTable ec boundary) preparedEndDepthPython)
    (pf : PFunc) (fn : Nat) (checked : preparedCodeVariableCheck pf fn pub=true)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0) (isEnd : tr.cell 0 r 469=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (sp : Nat)
    (state : PreparedExecState (tr.cell 0 r) s f [] sp)
    (func : p.funcs[f.fn]?=some pf) (labels : f.labels=[] ∨ ∃ lab,f.labels=[lab])
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    sp=0 ∧ step cfg p s=.fin {s with
      stack:=#[]
      frames:=[]
      stackRem:=s.stackRem+pf.stackCharge
      gas:={s.gas with g:=preparedExecWord64 (tr.cell 0 (r+1)) 299}} ∧
    tr.cell 0 (r+1) 41=1 ∧ tr.cell 0 (r+1) 42=0 := by
  have localH:=prepared_exec_table_local ec cc boundary count tr pub holds
  have hr : r<tr.height 0:=by omega
  obtain ⟨op,code,ops⟩:=prepared_exec_authenticated_opcode ec cc boundary count tr pub holds
    codeSource inactive pf fn checked r hr
  have tag:=ops 3 (by decide)
  rw [isEnd] at tag
  have opEq : op=PreparedPublicInstruction.end_ := by
    cases op <;> simp only [PreparedPublicInstruction.tag,Nat.reduceEqDiff,ite_false,ite_true] at tag ⊢
    all_goals first | rfl | exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  obtain ⟨_,charge,bounded⟩:=prepared_exec_authenticated_fee ec cc boundary count tr pub holds
    codeSource inactive pf fn checked r hr
  have enoughRow : preparedExecWord64 (tr.cell 0 r) 502≤preparedExecWord64 (tr.cell 0 r) 299 := by
    rw [←state.gas];exact enough
  obtain ⟨borrow,gasNext⟩:=prepared_exec_gas_success _ tr 0 r pub gasSource localH nonlast active enoughRow
  have depth:=prepared_exec_source_eval _ tr 0 r pub localH nonlast _ guard
  have depthEq : preparedExecLower preparedEndDepthPython=
      .mul (.mul (.add (.const 1) (.neg (.col 41 false))) (.add (.const 1) (.neg (.col 430 false))))
        (.mul (.col 469 false) (.add (.const 1) (.neg (.col 32 false)))) := rfl
  rw [depthEq] at depth
  change (((1:Fp)+ -tr.cell 0 r 41)*((1:Fp)+ -tr.cell 0 r 430))*
    (tr.cell 0 r 469*((1:Fp)+ -tr.cell 0 r 32))=0 at depth
  rw [active,borrow,isEnd] at depth
  have emptySP : tr.cell 0 r 32=1 := by grind
  have selected:=state.selected 0 (by decide)
  have spZero : sp=0 := by
    change tr.cell 0 r 32=(if 0=sp then 1 else 0) at selected
    rw [emptySP] at selected
    by_cases z:0=sp
    · omega
    · simp only [z,ite_false] at selected
      exact False.elim ((by decide : (1:Fp)≠0) selected)
  have emptyStack : s.stack=#[] := by rw [state.stack,spZero];rfl
  have run:=prepared_wasm_end cfg p s f pf (preparedExecWord64 (tr.cell 0 r) 502)
    state.frames func (by rw [state.pc];exact code) labels emptyStack
    (by rw [state.pc];exact charge) bounded enough
  have flags:=prepared_exec_terminal_flags _ tr 0 r pub localH nonlast source active
  refine ⟨spZero,?_,?_,?_⟩
  · rw [gasNext,←state.gas];exact run
  · rw [active,borrow,isEnd] at flags
    grind
  · exact flags.2.1.trans borrow

end NearCompression
