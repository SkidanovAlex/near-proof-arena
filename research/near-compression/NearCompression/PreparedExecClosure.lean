import NearCompression.PreparedExecState

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

def preparedExecSPChoice : Expr :=
  .add (.add (preparedBalancedSum (fun i=>.col (32+i) false) 3 0) (.col 40 false)) (.neg (.const 1))
structure PreparedExecClosureSource (table : Table) : Prop where
  localSource : PreparedExecLocalSource table
  sp : preparedExecSPChoice∈table.constraints
  invariant : PreparedExecHasSource table preparedFailureInvariantPython
  done : PreparedExecHasSource table preparedDoneStepPython
  failed : PreparedExecHasSource table preparedFailureStepPython

theorem prepared_exec_sp_onehot (table : Table) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal table tr t pub) (hr : r<tr.height t) (source : PreparedExecClosureSource table) :
    ∃ sp,sp<9 ∧ ∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0 := by
  apply prepared_onehot 9 32 (tr.cell t r) (by decide)
  · intro i hi
    apply instruction_add_boolean_bound
    have h:=prepared_exec_table_boolean table tr t r pub localH hr source.localSource (32+i) (by omega)
    grind
  · have h:=localH.constr r hr _ source.sp
    simp only [preparedExecSPChoice,preparedBalancedSum,Expr.eval,Expr.evalWith,rowEnv,
      Nat.reduceAdd,Nat.reducePow,Bool.false_eq_true,ite_false] at h
    simp only [preparedFieldSum,Nat.reduceAdd]
    try simp only [←Fp.ofNat_def] at h
    grind

theorem prepared_exec_opcode_projection (row next pub : Nat → Fp) (tag : Nat)
    (op : ∀ i,i<4 → row (466+i)=if i=tag then 1 else 0) :
    ∀ i,i<4 → (preparedFetchPython i).evalWith
      (preparedRowEnv (preparedExecGhostRow row) (preparedExecGhostNext row next pub)
        (preparedExecGhostPub row next pub) 0 0)=if i=tag then 1 else 0 := by
  intro i hi
  rw [←prepared_exec_lower_eval,prepared_exec_fetch_lower i (by omega)]
  simp only [hi,ite_true,preparedExecSimplify,Expr.evalWith,preparedRowEnv]
  exact op i hi

theorem prepared_exec_ghost_next_column (row next pub : Nat → Fp) (c : Nat) (hc : 16≤c) :
    preparedExecGhostNext row next pub c=next (c+16) := by
  simp only [preparedExecGhostNext,preparedExecOldCol,ite_eq_right (by omega : ¬c<16),
    Expr.evalWith,preparedRowEnv,ite_true]

theorem prepared_exec_next_stack (row next pub : Nat → Fp) (sp : Nat) :
    preparedWasmStack (preparedExecGhostNext row next pub) sp=
      preparedWasmStack (preparedExecGhostRow next) sp := by
  apply prepared_wasm_stack_congr
  intro i hi
  simp (disch:=omega) only [preparedStackWord,instructionBitExpr,Expr.evalWith,instructionAddEnv,
    prepared_exec_ghost_next_column,preparedExecGhostRow,ite_eq_right]

theorem prepared_exec_add_next_sp (table : Table) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal table tr t pub) (nonlast : r+1<tr.height t) (source : PreparedExecClosureSource table)
    (active : tr.cell t r 41=0) (noBorrow : tr.cell t r 430=0)
    (op : ∀ i,i<4 → tr.cell t r (466+i)=if i=1 then 1 else 0)
    (sp : Nat) (hs : sp<9) (selected : ∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) :
    1≤sp ∧ sp-1<9 ∧ ∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=sp-1 then 1 else 0 := by
  have projection:=prepared_exec_table_projection table tr t r pub localH nonlast source.localSource
  obtain ⟨nsp,hn,hot⟩:=prepared_exec_sp_onehot table tr t (r+1) pub localH nonlast source
  have opOld:=prepared_exec_opcode_projection (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0) 1 op
  have activeOld : preparedExecGhostRow (tr.cell t r) 25=0 := active
  have noBorrowOld : preparedExecGhostRow (tr.cell t r) 414=0 := noBorrow
  have success:=(prepared_success_advance _ _ _ activeOld noBorrowOld opOld).1
  have current : ∀ i,i<9 → preparedExecGhostRow (tr.cell t r) (16+i)=if i=sp then 1 else 0 := by
    intro i hi
    simpa [preparedExecGhostRow,show ¬16+i<16 by omega,show ¬i+16<16 by omega,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using selected i hi
  have following : ∀ i,i<9 → preparedExecGhostNext (tr.cell t r) (tr.cell t (r+1))
      (fun i=>pub.getD i 0) (16+i)=if i=nsp then 1 else 0 := by
    intro i hi
    rw [prepared_exec_ghost_next_column _ _ _ _ (by omega)]
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hot i hi
  have eq:=prepared_add_sp_next _ _ _ projection.2 success opOld sp nsp hs hn current following
  have ns : nsp=sp-1:=by omega
  exact ⟨by omega,by omega,by simpa only [ns] using hot⟩

theorem prepared_exec_success_flags (table : Table) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal table tr t pub) (nonlast : r+1<tr.height t) (source : PreparedExecClosureSource table)
    (active : tr.cell t r 41=0) (noBorrow : tr.cell t r 430=0) (notEnd : tr.cell t r 469=0) :
    tr.cell t r 42=0 ∧ tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 := by
  have success : preparedSuccessExpr.evalWith (preparedRowEnv
      (preparedExecGhostRow (tr.cell t r))
      (preparedExecGhostNext (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0))
      (preparedExecGhostPub (tr.cell t r) (tr.cell t (r+1)) (fun i=>pub.getD i 0)) 0 0)=1 := by
    change ((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430)=1
    rw [active,noBorrow];grind
  have result:=prepared_success_flags _ _ _ active noBorrow success
    (by rw [←prepared_exec_lower_eval];exact notEnd)
    ((prepared_exec_lower_eval _ _ _ _).symm.trans
      (prepared_exec_source_eval table tr t r pub localH nonlast _ source.invariant))
    ((prepared_exec_lower_eval _ _ _ _).symm.trans
      (prepared_exec_source_eval table tr t r pub localH nonlast _ source.done))
    ((prepared_exec_lower_eval _ _ _ _).symm.trans
      (prepared_exec_source_eval table tr t r pub localH nonlast _ source.failed))
  exact result

/-- Complete successor-state preservation for authenticated successful add,
including selected next height and nonterminal flags. Entry/PREP binding and
source-certificate construction remain explicit external interfaces. -/
theorem prepared_exec_authenticated_add_closed (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedCodeBusAir ec cc boundary count) pub tr)
    (codeSource : PreparedCodeOrderSource (preparedCodeDataTable cc))
    (inactive : ∀ i,i<25 → preparedCodeInactive (172+i)∈cc)
    (source : PreparedExecClosureSource (preparedCodeExecTable ec boundary))
    (gasSource : PreparedExecGasSource (preparedCodeExecTable ec boundary))
    (pf : PFunc) (fn : Nat) (checked : preparedCodeVariableCheck pf fn pub=true)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0) (isAdd : tr.cell 0 r 467=1)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame) (sp : Nat)
    (state : PreparedExecState (tr.cell 0 r) s f fs sp)
    (func : p.funcs[f.fn]?=some pf)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    ∃ s',step cfg p s=.cont s' ∧
      PreparedExecState (tr.cell 0 (r+1)) s'
        {f with pc:=preparedCodeExecPC (tr.cell 0 (r+1))} fs (sp-1) ∧
      tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0 := by
  have localH:=prepared_exec_table_local ec cc boundary count tr pub holds
  obtain ⟨op,code,ops⟩:=prepared_exec_authenticated_opcode ec cc boundary count tr pub holds
    codeSource inactive pf fn checked r (by omega)
  have tag:=ops 1 (by decide)
  rw [isAdd] at tag
  have opEq : op=PreparedPublicInstruction.add := by
    cases op <;> simp only [PreparedPublicInstruction.tag,Nat.reduceEqDiff,ite_false,ite_true] at tag ⊢
    all_goals first | rfl | exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  have enoughRow : preparedExecWord64 (tr.cell 0 r) 502≤preparedExecWord64 (tr.cell 0 r) 299 := by
    rw [←state.gas];exact enough
  obtain ⟨noBorrow,_⟩:=prepared_exec_gas_success _ tr 0 r pub gasSource localH nonlast active enoughRow
  obtain ⟨_,height,hot⟩:=prepared_exec_add_next_sp _ tr 0 r pub localH nonlast source active noBorrow
    ops sp state.depth state.selected
  have endZero:=ops 3 (by decide)
  simp only [PreparedPublicInstruction.tag,Nat.reduceEqDiff,ite_false] at endZero
  have flags:=prepared_exec_success_flags _ tr 0 r pub localH nonlast source active noBorrow endZero
  have run:=prepared_exec_authenticated_add ec cc boundary count tr pub holds codeSource inactive
    source.localSource gasSource pf fn checked r nonlast active isAdd cfg p s f fs sp state func enough
  rw [prepared_exec_next_stack] at run
  refine ⟨_,run,?_,flags.2.1,flags.2.2⟩
  exact ⟨height,hot,rfl,rfl,rfl,rfl⟩

end NearCompression
