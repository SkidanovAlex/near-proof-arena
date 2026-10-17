import NearCompression.PreparedControlAuthenticated
import NearCompression.PreparedControlStack
set_option maxRecDepth 65536
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

theorem prepared_control_terminal_flags (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (nonlast : r+1<tr.height t)
    (active : tr.cell t r 41=0) :
    tr.cell t r 42=0 ∧ tr.cell t (r+1) 42=tr.cell t r 430 ∧
    tr.cell t (r+1) 41=tr.cell t r 430+
      ((1-tr.cell t r 41)*(1-tr.cell t r 430))*(tr.cell t r 469*(1-tr.cell t r 639)) := by
  have invariant:=localH.constr r (by omega) preparedControlLiteralExec0684
    (List.getElem_mem (l:=preparedControlLiteralExec) (n:=684) (by decide))
  change tr.cell t r 42*((1:Fp)+ -tr.cell t r 41)+ -(0:Fp)=0 at invariant
  rw [active] at invariant
  have failed : tr.cell t r 42=0:=by grind
  have done:=localH.constr r (by omega) preparedControlLiteralExec0728
    (List.getElem_mem (l:=preparedControlLiteralExec) (n:=728) (by decide))
  have fail:=localH.constr r (by omega) preparedControlLiteralExec0729
    (List.getElem_mem (l:=preparedControlLiteralExec) (n:=729) (by decide))
  change (if r+1=tr.height t then (0:Fp) else 1)*(tr.cell t ((r+1)%tr.height t) 41+
    -(tr.cell t r 41+(((1:Fp)+ -tr.cell t r 41)*tr.cell t r 430+
      (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*(tr.cell t r 469*((1:Fp)+ -tr.cell t r 639)))))=0 at done
  change (if r+1=tr.height t then (0:Fp) else 1)*(tr.cell t ((r+1)%tr.height t) 42+
    -(tr.cell t r 42+((1:Fp)+ -tr.cell t r 41)*tr.cell t r 430))=0 at fail
  rw [if_neg (by omega),Nat.mod_eq_of_lt nonlast,active] at done fail
  rw [failed] at fail
  exact ⟨failed,by grind,by rw [active];grind⟩

theorem prepared_control_root_height_zero (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (hr : r<tr.height t)
    (absent : tr.cell t r 639=0) : ∀ i,i<9 → tr.cell t r (640+i)=0 := by
  have h:=localH.constr r hr preparedControlLiteralExec0683
    (List.getElem_mem (l:=preparedControlLiteralExec) (n:=683) (by decide))
  change (((tr.cell t r 640+tr.cell t r 641)+(tr.cell t r 642+tr.cell t r 643))+
    ((tr.cell t r 644+tr.cell t r 645)+(tr.cell t r 646+tr.cell t r 647))+tr.cell t r 648)+ -tr.cell t r 639=0 at h
  rw [absent] at h
  have sum : preparedFieldSum 9 (fun i=>tr.cell t r (640+i))=0 := by
    simp only [preparedFieldSum,Nat.reduceAdd];grind
  have natSum:=prepared_sum_nat_bound 9 (fun i=>tr.cell t r (640+i)) (by decide)
    (fun i hi=>prepared_control_literal_boolean tr t r pub localH hr _ (by omega))
  rw [sum] at natSum
  intro i hi
  apply Fp.ext
  change (tr.cell t r (640+i)).toNat=0
  exact prepared_nat_sum_zero 9 _ natSum.1.symm i hi

theorem prepared_control_root_end_depth (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub) (hr : r<tr.height t)
    (active : tr.cell t r 41=0) (charged : tr.cell t r 430=0)
    (isEnd : tr.cell t r 469=1) (absent : tr.cell t r 639=0)
    (sp : Nat) (hs : sp<9) (selected : ∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) : sp=0 := by
  have empty:=prepared_control_root_height_zero tr t r pub localH hr absent
  have z0:=empty 0 (by decide);have z1:=empty 1 (by decide);have z2:=empty 2 (by decide)
  have z3:=empty 3 (by decide);have z4:=empty 4 (by decide);have z5:=empty 5 (by decide)
  have z6:=empty 6 (by decide);have z7:=empty 7 (by decide);have z8:=empty 8 (by decide)
  have saved : (preparedControlIndex 640).eval tr t r pub=0 := by
    simp only [preparedControlIndex,preparedBalancedSum,Expr.eval,Expr.evalWith,rowEnv,Nat.reducePow,Nat.reduceAdd,Bool.false_eq_true,ite_false]
    simp only [Nat.reduceAdd] at z0 z1 z2 z3 z4 z5 z6 z7 z8
    rw [z0,z1,z2,z3,z4,z5,z6,z7,z8];grind
  have h:=localH.constr r hr preparedControlLiteralExec0770
    (List.getElem_mem (l:=preparedControlLiteralExec) (n:=770) (by decide))
  change (((1:Fp)+ -tr.cell t r 41)*((1:Fp)+ -tr.cell t r 430))*
    (tr.cell t r 469*((preparedControlIndex 32).eval tr t r pub+ -(preparedControlIndex 640).eval tr t r pub))+ -(0:Fp)=0 at h
  have current : (preparedControlIndex 32).eval tr t r pub=Fp.ofNat sp:=prepared_control_index_selected (tr.cell t r) 32 sp hs selected
  rw [active,charged,isEnd,saved,current] at h
  have zero : Fp.ofNat sp=0:=by grind
  have natZero:=congrArg Fp.toNat zero
  rw [Fp.toNat_ofNat] at natZero
  change sp%ZkFormal.Algebra.P=0 at natZero
  rw [Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega)] at natZero
  exact natZero

theorem prepared_control_setup_exhaustion (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedControlSetupCheck cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedControlState (tr.cell 0 r) s f fs sp root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (context : PreparedWasmGasContext s)
    (insufficient : s.gas.g<preparedExecWord64 (tr.cell 0 r) 502) :
    step cfg eligible.setup.program s=.abort {s with gas:=preparedWasmFailureGas s (preparedExecWord64 (tr.cell 0 r) 502)}
      (preparedWasmFailureError s (preparedExecWord64 (tr.cell 0 r) 502)) ∧
    tr.cell 0 (r+1) 41=1 ∧ tr.cell 0 (r+1) 42=1 ∧
    preparedExecWord64 (tr.cell 0 (r+1)) 299=s.gas.g := by
  have localH:=prepared_control_exec_local count tr pub holds
  obtain ⟨setup,func,checked⟩:=prepared_control_setup_checked cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨_,op,code,charge,bound,_,_⟩:=prepared_control_authenticated_decode count tr pub holds eligible.func _ checked r (by omega)
  rw [←state.1.pc] at code charge
  have insufficientRow : preparedExecWord64 (tr.cell 0 r) 299<preparedExecWord64 (tr.cell 0 r) 502 := by rw [←state.1.gas];exact insufficient
  obtain ⟨borrow,frozen⟩:=prepared_control_gas_exhaustion _ tr 0 r pub prepared_control_literal_gas_source localH nonlast insufficientRow
  have flags:=prepared_control_terminal_flags tr 0 r pub localH nonlast active
  have run:=prepared_wasm_exhaustion_trap cfg eligible.setup.program s f fs eligible.func op.instr (preparedExecWord64 (tr.cell 0 r) 502)
    state.1.frames (by rw [fn];exact func) code charge bound insufficient context
  refine ⟨run,?_,flags.2.1.trans borrow,frozen.trans state.1.gas.symm⟩
  rw [borrow] at flags;grind

theorem prepared_control_setup_root_end (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedControlSetupCheck cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (isEnd : tr.cell 0 r 469=1) (absent : tr.cell 0 r 639=0)
    (s : St) (f : Frame) (sp : Nat) (root : Label)
    (state : PreparedControlState (tr.cell 0 r) s f [] sp root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    sp=0 ∧ step cfg eligible.setup.program s=.fin {s with
      stack:=#[]
      frames:=[]
      stackRem:=s.stackRem+eligible.func.stackCharge
      gas:={s.gas with g:=preparedExecWord64 (tr.cell 0 (r+1)) 299}} ∧
    tr.cell 0 (r+1) 41=1 ∧ tr.cell 0 (r+1) 42=0 := by
  have localH:=prepared_control_exec_local count tr pub holds
  obtain ⟨setup,func,checked⟩:=prepared_control_setup_checked cfg bytes method ctx pub blockLevel eligible accepted
  obtain ⟨_,op,code,charge,bound,ops,_⟩:=prepared_control_authenticated_decode count tr pub holds eligible.func _ checked r (by omega)
  have tag:=ops 3 (by decide)
  change tr.cell 0 r 469=(if 3=op.tag then 1 else 0) at tag
  rw [isEnd] at tag
  have opEq : op=PreparedControlInstruction.legacy .end_ := by
    cases op with
    | block => exact False.elim ((by decide : (1:Fp)≠0) tag)
    | brIf => exact False.elim ((by decide : (1:Fp)≠0) tag)
    | legacy old => cases old <;> first | rfl | exact False.elim ((by decide : (1:Fp)≠0) tag)
  subst op
  rw [←state.1.pc] at code charge
  have enoughRow : preparedExecWord64 (tr.cell 0 r) 502≤preparedExecWord64 (tr.cell 0 r) 299 := by rw [←state.1.gas];exact enough
  obtain ⟨borrow,gas⟩:=prepared_control_gas_success _ tr 0 r pub prepared_control_literal_gas_source localH nonlast active enoughRow
  have depth:=prepared_control_root_end_depth tr 0 r pub localH (by omega) active borrow isEnd absent sp state.1.depth state.1.selected
  have labels : f.labels=[root] := by
    rcases state.2 with h|⟨height,_,present,_,_⟩
    · exact h.2
    · rw [absent] at present
      exact False.elim ((by decide : (0:Fp)≠1) present)
  have emptyStack : s.stack=#[] := by rw [state.1.stack,depth];rfl
  have run:=prepared_wasm_end cfg eligible.setup.program s f eligible.func (preparedExecWord64 (tr.cell 0 r) 502)
    state.1.frames (by rw [fn];exact func) code (Or.inr ⟨root,labels⟩) emptyStack charge bound enough
  have flags:=prepared_control_terminal_flags tr 0 r pub localH nonlast active
  refine ⟨depth,?_,?_,flags.2.1.trans borrow⟩
  · rw [gas,←state.1.gas];exact run
  · rw [borrow,isEnd,absent,active] at flags;grind

end NearCompression
