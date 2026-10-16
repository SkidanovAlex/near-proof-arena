import NearCompression.PreparedCodeReachability
import NearCompression.PreparedWasmEntry

namespace NearCompression
open ZkFormal.Algebra ZkFormal.Air NearSpecV3.Wasm

/-- Exact source last-row residual, including subtraction from one. -/
def preparedLastDonePython : Expr := .mul .isLast (.add (.col 25 false) (.neg (.const 1)))

theorem prepared_last_done (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (member : preparedLastDonePython∈table.constraints)
    (positive : 0<tr.height t) : tr.cell t (tr.height t-1) 25=1 := by
  have last:=localH.constr (tr.height t-1) (by omega) preparedLastDonePython member
  rw [Expr.eval,prepared_gas_row_env] at last
  have eq : tr.height t-1+1=tr.height t := by omega
  simp only [preparedLastDonePython,Expr.evalWith,preparedRowEnv,eq,ite_true,
    Bool.false_eq_true,ite_false,←Fp.ofNat_def] at last
  grind

theorem prepared_public_classification (row next : Nat → Fp) (pub : List Fp) (pc tagValue : Nat)
    (hpc : pc<16) (selected : ∀ i,i<16 → row i=if i=pc then 1 else 0)
    (tags : ∀ tag,tag<4 → (preparedFetchPython tag).evalWith
      (preparedRowEnv row next (fun i=>pub.getD i 0) 0 0)=if tag=tagValue then 1 else 0) :
    ∀ q,q<16 → row q=1 → ∀ tag,tag<4 → pub.getD (56+10*q+tag) 0=if tag=tagValue then 1 else 0 := by
  intro q hq one tag ht
  have sel:=selected q hq
  have same : q=pc := by
    by_cases eq:q=pc
    · exact eq
    · rw [ite_eq_right eq,one] at sel
      exact False.elim ((by decide : (1:Fp)≠0) sel)
  subst q
  have h:=tags tag ht
  rw [prepared_fetch_python_eval,prepared_fetch_selected row next _ 0 0 pc hpc selected] at h
  exact h

/-- Successor row/state bindings and active status are consequences of the
source AIR, allowing certificate construction rather than assuming each tail. -/
theorem prepared_wasm_continue_row (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (air : PreparedWasmAir table tr t pub) (cfg : NearCfg) (p : Prepared) (r : Nat) (s : St)
    (c : PreparedWasmContinue p tr t r pub s) :
    tr.cell t (r+1) 25=0 ∧
    PreparedWasmState (tr.cell t (r+1)) pub c.next
      {c.location.frame with pc:=c.location.pc+1} c.location.outer
      (c.location.pc+1) (preparedWasmNextSP c.op c.location.sp) := by
  rcases c with ⟨loc,op,nonlast,active,enough,publicOp,code⟩
  rcases op with _ | push
  · obtain ⟨out,_,eq,state⟩:=prepared_table_wasm_add table air.source.terminal.gasMiddle air.source.terminal.gasTail
      air.source.prefixPart air.source.middle air.source.dead air.source.terminal.gasSource air.source.transition
      air.source.depth air.source.terminal.flagMembers air.source.carries air.source.terminal.gasMembers
      tr t r pub air.localH nonlast active air.fees publicOp enough cfg p s loc.frame loc.outer loc.func
      loc.pc loc.sp loc.state loc.fetchFunc code loc.charge
    have projection:=prepared_table_local_add table air.source.terminal.gasMiddle air.source.terminal.gasTail
      air.source.prefixPart air.source.middle air.source.dead air.source.terminal.gasSource air.source.transition
      air.source.depth air.source.terminal.flagMembers air.source.carries air.source.terminal.gasMembers
      tr t r pub air.localH nonlast active air.fees publicOp enough
    rw [eq] at state
    exact ⟨projection.2.1,state⟩
  · obtain ⟨out,_,eq,state⟩:=prepared_table_wasm_const_drop push table air.source.terminal air.source.prefixPart air.source.middle
      air.source.dead air.source.transition tr t r pub air.localH nonlast active air.fees air.immediates
      (by cases push <;> exact publicOp) enough cfg p s loc.frame loc.outer loc.func loc.pc loc.sp loc.state
      loc.fetchFunc (by cases push <;> exact code) loc.charge
    have projection:=prepared_table_const_drop push table air.source.terminal air.source.prefixPart air.source.middle
      air.source.dead air.source.transition tr t r pub air.localH nonlast active air.fees air.immediates
      (by cases push <;> exact publicOp) enough
    rw [eq] at state
    refine ⟨projection.2.1,?_⟩
    cases push <;> exact state

/-- Construct the finite execution certificate from local AIR validity and a
checked real prepared program. Live-PC reachability is propagated internally;
no per-row interpreter trace or code/charge equations are assumed. -/
theorem prepared_wasm_construct_execution (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (air : PreparedWasmAir table tr t pub) (lastMember : preparedLastDonePython∈table.constraints)
    (cfg : NearCfg) (p : Prepared) (pf : PFunc)
    (checked : preparedCodeTerminatedCheck pf pub=true)
    (fuel : Nat) (r : Nat) (s : St) (f : Frame) (pc sp : Nat)
    (remaining : pf.code.size-pc=fuel) (live : pc<pf.code.size) (hr : r<tr.height t)
    (active : tr.cell t r 25=0) (state : PreparedWasmState (tr.cell t r) pub s f [] pc sp)
    (func : p.funcs[f.fn]?=some pf) (labels : f.labels=[] ∨ ∃ lab,f.labels=[lab]) :
    ∃ n final error,n≤fuel ∧ PreparedWasmExecution p tr t pub r s n final error := by
  induction fuel generalizing r s f pc sp with
  | zero => omega
  | succ fuel ih =>
    have nonlast : r+1<tr.height t := by
      by_cases lt:r+1<tr.height t
      · exact lt
      · have endIndex : r=tr.height t-1 := by omega
        have last:=prepared_last_done table tr t pub air.localH lastMember (by omega)
        rw [←endIndex,active] at last
        exact False.elim ((by decide : (0:Fp)≠1) last)
    have shape:=prepared_code_terminated_shape pf pub checked
    have selected:=state.2.2.1
    have hpc:=state.1
    have fpc:=state.2.2.2.2.2.1
    obtain ⟨op,code,charge,tags,immediate⟩:=prepared_code_selected_fee pf pub shape.1 pc live hpc
      (tr.cell t r) (tr.cell t (r+1)) selected
    have publicOp:=prepared_public_classification (tr.cell t r) (tr.cell t (r+1)) pub pc op.tag hpc selected tags
    let loc : PreparedWasmLocation p (tr.cell t r) pub s :=
      ⟨f,[],pf,pc,sp,state,func,by rw [fpc];exact charge⟩
    by_cases enough : preparedFeeValue (tr.cell t r) pub≤preparedGasValue (tr.cell t r) pub
    · have advance (opcode : Option Bool) (classification : op.tag=preparedWasmOpTag opcode)
          (instruction : op.instr=preparedWasmOpInstr (tr.cell t r) (tr.cell t (r+1)) pub opcode)
          (notEnd : op.instr≠.end_) :
          ∃ n final error,n≤fuel+1 ∧ PreparedWasmExecution p tr t pub r s n final error := by
        let c : PreparedWasmContinue p tr t r pub s :=
          ⟨loc,opcode,nonlast,active,enough,by rw [←classification];exact publicOp,
            by change pf.code[f.pc]?=_;rw [fpc,code,instruction]⟩
        have nextLive:=prepared_code_live_successor pf pub pc op.instr checked live code notEnd
        have nextRow:=prepared_wasm_continue_row table tr t pub air cfg p r s c
        have nextState : PreparedWasmState (tr.cell t (r+1)) pub c.next {f with pc:=pc+1} []
            (pc+1) (preparedWasmNextSP opcode sp) := nextRow.2
        obtain ⟨n,final,error,count,tail⟩:=ih (r+1) c.next {f with pc:=pc+1} (pc+1)
          (preparedWasmNextSP opcode sp) (by omega) nextLive nonlast nextRow.1 nextState func labels
        exact ⟨n+1,final,error,Nat.add_le_add_right count 1,.advance c tail⟩
      cases op with
      | constant value =>
        apply advance (some true) rfl
        · change Instr.i32Const value=Instr.i32Const (UInt32.ofNat (preparedImmediateWord _ _ _))
          rw [immediate]
          simp only [PreparedPublicInstruction.immediate,UInt32.ofNat_toNat]
        · intro impossible;cases impossible
      | add =>
        apply advance none rfl rfl
        intro impossible;cases impossible
      | drop =>
        apply advance (some false) rfl rfl
        intro impossible;cases impossible
      | end_ =>
        let c : PreparedWasmEnd p tr t r pub s :=
          ⟨loc,rfl,labels,nonlast,active,enough,publicOp,by change pf.code[f.pc]?=_;rw [fpc];exact code⟩
        exact ⟨1,c.final,none,by omega,.finish c⟩
    · let c : PreparedWasmExhausted p tr t r pub s :=
        ⟨loc,op.instr,by change pf.code[f.pc]?=_;rw [fpc];exact code,
          nonlast,active,Nat.lt_of_not_ge enough⟩
      exact ⟨1,c.final,some c.error,by omega,.fail c⟩

/-- Source first-row selectors used to bind the actual entry frame and stack. -/
def preparedFirstEqPython (column : Nat) (value : Nat) : Expr :=
  .mul .isFirst (.add (.col column false) (.neg (.const value)))

theorem prepared_first_value (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (localH : ZkFormal.Near.TableLocal table tr t pub) (column : Nat) (value : Nat)
    (member : preparedFirstEqPython column value∈table.constraints) (positive : 0<tr.height t) :
    tr.cell t 0 column=Fp.ofNat value := by
  have first:=localH.constr 0 positive (preparedFirstEqPython column value) member
  rw [Expr.eval,prepared_gas_row_env] at first
  simp only [preparedFirstEqPython,Expr.evalWith,preparedRowEnv,ite_true,Bool.false_eq_true,ite_false] at first
  grind

/-- First-row local constraints bind PC=0, SP=0 and the genuine entry stack.
Only the numeric initial gas binding remains a public-boundary premise. -/
theorem prepared_wasm_initial_state (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (air : PreparedWasmAir table tr t pub) (positive : 0<tr.height t)
    (firstPC : preparedFirstEqPython 0 1∈table.constraints)
    (firstSP : preparedFirstEqPython 16 1∈table.constraints)
    (p : Prepared) (fi : Nat) (pf : PFunc) (host : St)
    (initialGas : preparedGasValue (tr.cell t 0) pub=host.gas.remaining-pf.prologueGas) :
    PreparedWasmState (tr.cell t 0) pub (preparedWasmEntryState p fi pf host)
      (preparedWasmEntryFrame p fi pf) [] 0 0 := by
  have choices:=prepared_table_row_choices table air.source.terminal.gasMiddle air.source.terminal.gasTail
    air.source.terminal.gasSource tr t 0 pub air.localH positive (tr.cell t 0)
  obtain ⟨⟨pc,hpc,pcs⟩,⟨sp,hsp,sps⟩⟩:=prepared_row_pc_sp _ _ _ 0 0 choices
  have pcValue:=prepared_first_value table tr t pub air.localH 0 1 firstPC positive
  have spValue:=prepared_first_value table tr t pub air.localH 16 1 firstSP positive
  have zeroPC : pc=0 := by
    have h:=pcs 0 (by decide)
    rw [pcValue] at h
    by_cases eq:0=pc
    · exact eq.symm
    · simp only [eq,ite_false] at h
      exact False.elim ((by decide : (1:Fp)≠0) h)
  have zeroSP : sp=0 := by
    have h:=sps 0 (by decide)
    simp only [Nat.add_zero,spValue] at h
    by_cases eq:0=sp
    · exact eq.symm
    · simp only [eq,ite_false] at h
      exact False.elim ((by decide : (1:Fp)≠0) h)
  subst pc;subst sp
  exact ⟨by decide,by decide,pcs,sps,rfl,rfl,rfl,initialGas.symm⟩

/-- Actual callEntry execution constructed from valid local AIR and inspected
prepared code, without assuming a certificate or an enter/step equation.
Initial public fast-gas provenance is the remaining entry boundary. -/
theorem prepared_wasm_air_call_entry (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (source : PreparedWasmSource table) (localH : ZkFormal.Near.TableLocal table tr t pub)
    (lastMember : preparedLastDonePython∈table.constraints)
    (firstPC : preparedFirstEqPython 0 1∈table.constraints)
    (firstSP : preparedFirstEqPython 16 1∈table.constraints)
    (firstActive : preparedFirstEqPython 25 0∈table.constraints)
    (positive : 0<tr.height t) (cfg : NearCfg) (p : Prepared) (fi : Nat) (pf : PFunc) (host : St)
    (checked : preparedCodeTerminatedCheck pf pub=true)
    (fetch : p.funcs[fi-p.m.imports.size]?=some pf)
    (stackBudget : pf.stackCharge≤host.stackRem)
    (feeBound : pf.prologueGas<u64Bound) (enough : pf.prologueGas≤host.gas.remaining)
    (promises : host.gas.promises=0) (limit : host.gas.limit=host.gas.prepaid)
    (spent : host.gas.burnt≤host.gas.prepaid) (prepaid : host.gas.prepaid≤maxGasBurnt)
    (initialGas : preparedGasValue (tr.cell t 0) pub=host.gas.remaining-pf.prologueGas) (extra : Nat) :
    ∃ n final error,n≤pf.code.size ∧
      PreparedWasmExecution p tr t pub 0 (preparedWasmEntryState p fi pf host) n final error ∧
      callEntry cfg p (pf.code.size+extra) host fi=.ok (final,error) := by
  have shape:=prepared_code_terminated_shape pf pub checked
  have bounds:=prepared_code_public_limb_bounds pf pub shape.1
  let air : PreparedWasmAir table tr t pub:=⟨source,localH,bounds.1,bounds.2⟩
  have state:=prepared_wasm_initial_state table tr t pub air positive firstPC firstSP p fi pf host initialGas
  have active:=prepared_first_value table tr t pub localH 25 0 firstActive positive
  obtain ⟨n,final,error,count,execution⟩:=prepared_wasm_construct_execution table tr t pub air lastMember cfg p pf
    checked pf.code.size 0 (preparedWasmEntryState p fi pf host) (preparedWasmEntryFrame p fi pf) 0 0
    (Nat.sub_zero _) shape.2.1 positive active state fetch (Or.inr ⟨_,rfl⟩)
  refine ⟨n,final,error,count,execution,?_⟩
  have actual:=prepared_wasm_checked_call_entry table tr t pub air cfg p host fi pf fetch stackBudget
    feeBound enough promises limit spent prepaid 0 n final error execution (pf.code.size+extra-n)
  have fuel : n+(pf.code.size+extra-n)=pf.code.size+extra := by omega
  rw [fuel] at actual
  exact actual

end NearCompression
