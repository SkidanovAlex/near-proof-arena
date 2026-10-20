import NearCompression.PreparedWasmAddStep
import NearCompression.PreparedWasmTerminal

namespace NearCompression
open ZkFormal.Algebra ZkFormal.Air NearSpecV3.Wasm

/-- Exact source-table fragments used by all five instruction cases. -/
structure PreparedWasmSource (table : Table) where
  terminal : PreparedTerminalSource table
  prefixPart : List Expr
  middle : List Expr
  dead : Nat → Nat → Expr
  transition : table.constraints=preparedAddTransitionSource prefixPart middle dead
  depth : preparedAddDepthSource∈table.constraints
  carries : ∀ i,i<2 → preparedAddCarryPython i∈table.constraints
  endDepth : preparedEndDepthPython∈table.constraints

structure PreparedWasmAir (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp) where
  source : PreparedWasmSource table
  localH : ZkFormal.Near.TableLocal table tr t pub
  fees : ∀ pc,pc<16 → ∀ limb,limb<4 → (pub.getD (56+10*pc+(6+limb)) 0).toNat<65536
  immediates : ∀ pc,pc<16 → ∀ limb,limb<2 → (pub.getD (56+10*pc+(4+limb)) 0).toNat<65536

/-- Actual prepared function/state provenance. It contains no step equation. -/
structure PreparedWasmLocation (p : Prepared) (row : Nat → Fp) (pub : List Fp) (s : St) where
  frame : Frame
  outer : List Frame
  func : PFunc
  pc : Nat
  sp : Nat
  state : PreparedWasmState row pub s frame outer pc sp
  fetchFunc : p.funcs[frame.fn]?=some func
  charge : PreparedWasmCharge func frame.pc (preparedFeeValue row pub)

/-- `some true`=const, `some false`=drop, `none`=i32.add. -/
def preparedWasmOpTag : Option Bool → Nat
  | some true => 0
  | some false => 2
  | none => 1

def preparedWasmOpInstr (row next : Nat → Fp) (pub : List Fp) : Option Bool → Instr
  | some true => .i32Const (UInt32.ofNat (preparedImmediateWord row next (fun i=>pub.getD i 0)))
  | some false => .drop
  | none => .num 0x6A

def preparedWasmNextSP (op : Option Bool) (sp : Nat) : Nat :=
  match op with | some true => sp+1 | _ => sp-1

structure PreparedWasmContinue (p : Prepared) (tr : Trace Fp) (t r : Nat) (pub : List Fp) (s : St) where
  location : PreparedWasmLocation p (tr.cell t r) pub s
  op : Option Bool
  nonlast : r+1<tr.height t
  active : tr.cell t r 25=0
  enough : preparedFeeValue (tr.cell t r) pub≤preparedGasValue (tr.cell t r) pub
  publicOp : ∀ pc,pc<16 → tr.cell t r pc=1 → ∀ tag,tag<4 →
    pub.getD (56+10*pc+tag) 0=if tag=preparedWasmOpTag op then 1 else 0
  code : location.func.code[location.frame.pc]?=some (preparedWasmOpInstr (tr.cell t r) (tr.cell t (r+1)) pub op)

def PreparedWasmContinue.next {p tr t r pub s} (c : PreparedWasmContinue p tr t r pub s) : St :=
  {s with
    stack := preparedWasmStack (tr.cell t (r+1)) (preparedWasmNextSP c.op c.location.sp)
    frames := {c.location.frame with pc:=c.location.pc+1}::c.location.outer
    gas := {s.gas with g:=preparedGasValue (tr.cell t (r+1)) pub}}

/-- Concrete source AIR derives each continuing step. -/
theorem prepared_wasm_continue (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (air : PreparedWasmAir table tr t pub) (cfg : NearCfg) (p : Prepared) (r : Nat) (s : St)
    (c : PreparedWasmContinue p tr t r pub s) :
    step cfg p s=.cont c.next ∧
    preparedGasValue (tr.cell t (r+1)) pub=preparedGasValue (tr.cell t r) pub-preparedFeeValue (tr.cell t r) pub := by
  rcases c with ⟨loc,op,nonlast,active,enough,publicOp,code⟩
  rcases op with _ | push
  · have h:=prepared_table_wasm_add table air.source.terminal.gasMiddle air.source.terminal.gasTail
      air.source.prefixPart air.source.middle air.source.dead air.source.terminal.gasSource air.source.transition
      air.source.depth air.source.terminal.flagMembers air.source.carries air.source.terminal.gasMembers
      tr t r pub air.localH nonlast active air.fees publicOp enough cfg p s loc.frame loc.outer loc.func
      loc.pc loc.sp loc.state loc.fetchFunc code loc.charge
    obtain ⟨out,run,eq,_⟩:=h
    have projection:=prepared_table_local_add table air.source.terminal.gasMiddle air.source.terminal.gasTail
      air.source.prefixPart air.source.middle air.source.dead air.source.terminal.gasSource air.source.transition
      air.source.depth air.source.terminal.flagMembers air.source.carries air.source.terminal.gasMembers
      tr t r pub air.localH nonlast active air.fees publicOp enough
    exact ⟨by rw [run,eq];rfl,projection.2.2.2.1⟩
  · have h:=prepared_table_wasm_const_drop push table air.source.terminal air.source.prefixPart air.source.middle
      air.source.dead air.source.transition tr t r pub air.localH nonlast active air.fees air.immediates
      (by cases push <;> exact publicOp) enough cfg p s loc.frame loc.outer loc.func loc.pc loc.sp loc.state
      loc.fetchFunc (by cases push <;> exact code) loc.charge
    obtain ⟨out,run,eq,_⟩:=h
    have projection:=prepared_table_const_drop push table air.source.terminal air.source.prefixPart air.source.middle
      air.source.dead air.source.transition tr t r pub air.localH nonlast active air.fees air.immediates
      (by cases push <;> exact publicOp) enough
    refine ⟨?_,projection.2.2.2.1⟩
    rw [run,eq];cases push <;> rfl

theorem prepared_wasm_continue_gas (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (air : PreparedWasmAir table tr t pub) (cfg : NearCfg) (p : Prepared) (r : Nat) (s : St)
    (c : PreparedWasmContinue p tr t r pub s) (context : PreparedWasmGasContext s) :
    PreparedWasmGasContext c.next := by
  have gas:=(prepared_wasm_continue table tr t pub air cfg p r s c).2
  rcases c.location.state with ⟨_,_,_,_,_,_,_,current⟩
  rcases context with ⟨a,b,d,e,f⟩
  unfold PreparedWasmGasContext PreparedWasmContinue.next
  dsimp only
  refine ⟨a,b,d,?_,f⟩
  change preparedGasValue (tr.cell t (r+1)) pub≤s.gas.prepaid-s.gas.burnt
  rw [gas]
  rw [current] at e
  exact Nat.le_trans (Nat.sub_le _ _) e

structure PreparedWasmEnd (p : Prepared) (tr : Trace Fp) (t r : Nat) (pub : List Fp) (s : St) where
  location : PreparedWasmLocation p (tr.cell t r) pub s
  outerEmpty : location.outer=[]
  labels : location.frame.labels=[] ∨ ∃ lab,location.frame.labels=[lab]
  nonlast : r+1<tr.height t
  active : tr.cell t r 25=0
  enough : preparedFeeValue (tr.cell t r) pub≤preparedGasValue (tr.cell t r) pub
  publicEnd : ∀ pc,pc<16 → tr.cell t r pc=1 → ∀ tag,tag<4 →
    pub.getD (56+10*pc+tag) 0=if tag=3 then 1 else 0
  code : location.func.code[location.frame.pc]?=some .end_

def PreparedWasmEnd.raw {p tr t r pub s} (c : PreparedWasmEnd p tr t r pub s) : St :=
  {s with
    stack := #[]
    frames := []
    stackRem := s.stackRem+c.location.func.stackCharge
    gas := {s.gas with g:=preparedGasValue (tr.cell t (r+1)) pub}}

def PreparedWasmEnd.final {p tr t r pub s} (c : PreparedWasmEnd p tr t r pub s) : St :=
  {c.raw with gas:={c.raw.gas with burnt:=s.gas.prepaid-preparedGasValue (tr.cell t (r+1)) pub}}

theorem prepared_wasm_end_certificate (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (air : PreparedWasmAir table tr t pub) (cfg : NearCfg) (p : Prepared) (r : Nat) (s : St)
    (c : PreparedWasmEnd p tr t r pub s) (context : PreparedWasmGasContext s) :
    step cfg p s=.fin c.raw ∧ sync c.raw=.ok c.final := by
  have state : PreparedWasmState (tr.cell t r) pub s c.location.frame [] c.location.pc c.location.sp := by
    rw [←c.outerEmpty];exact c.location.state
  have finish:=prepared_table_wasm_end table air.source.terminal air.source.prefixPart air.source.middle
    air.source.dead air.source.transition air.source.endDepth tr t r pub air.localH c.nonlast c.active
    air.fees c.publicEnd c.enough cfg p s c.location.frame c.location.func c.location.pc c.location.sp
    state c.location.fetchFunc c.code c.labels c.location.charge
  have projected:=prepared_table_end table air.source.terminal air.source.prefixPart air.source.middle
    air.source.dead air.source.transition air.source.endDepth tr t r pub air.localH c.nonlast c.active
    air.fees c.publicEnd c.enough
  have current:=c.location.state.2.2.2.2.2.2.2
  have gas : preparedGasValue (tr.cell t (r+1)) pub=s.gas.g-preparedFeeValue (tr.cell t r) pub := by
    rw [projected.2.2.2.1,current]
  refine ⟨finish.2.2,?_⟩
  simpa only [PreparedWasmEnd.raw,PreparedWasmEnd.final,gas] using
    prepared_wasm_end_sync s c.location.func (preparedFeeValue (tr.cell t r) pub) context

structure PreparedWasmExhausted (p : Prepared) (tr : Trace Fp) (t r : Nat) (pub : List Fp) (s : St) where
  location : PreparedWasmLocation p (tr.cell t r) pub s
  ins : Instr
  code : location.func.code[location.frame.pc]?=some ins
  nonlast : r+1<tr.height t
  active : tr.cell t r 25=0
  exhausted : preparedGasValue (tr.cell t r) pub<preparedFeeValue (tr.cell t r) pub

def PreparedWasmExhausted.final {p tr t r pub s} (_ : PreparedWasmExhausted p tr t r pub s) : St :=
  {s with gas:=preparedWasmFailureGas s (preparedFeeValue (tr.cell t r) pub)}
def PreparedWasmExhausted.error {p tr t r pub s} (_ : PreparedWasmExhausted p tr t r pub s) : String :=
  preparedWasmFailureError s (preparedFeeValue (tr.cell t r) pub)

theorem prepared_wasm_exhausted_certificate (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (air : PreparedWasmAir table tr t pub) (cfg : NearCfg) (p : Prepared) (r : Nat) (s : St)
    (c : PreparedWasmExhausted p tr t r pub s) (context : PreparedWasmGasContext s) :
    step cfg p s=.abort c.final c.error ∧ sync c.final=.ok c.final := by
  have fail:=prepared_table_wasm_exhaustion table air.source.terminal tr t r pub air.localH c.nonlast c.active
    air.fees c.exhausted cfg p s c.location.frame c.location.outer c.location.func c.ins c.location.pc
    c.location.sp c.location.state c.location.fetchFunc c.code c.location.charge context
  exact ⟨fail.2.2.2,prepared_wasm_failure_sync s (preparedFeeValue (tr.cell t r) pub) context⟩

/-- Finite execution certificates use source instruction cases, never an assumed
list of interpreter step equalities. Rows are consumed consecutively. -/
inductive PreparedWasmExecution (p : Prepared) (tr : Trace Fp) (t : Nat) (pub : List Fp) :
    Nat → St → Nat → St → Option String → Prop where
  | finish {r s} (c : PreparedWasmEnd p tr t r pub s) :
      PreparedWasmExecution p tr t pub r s 1 c.final none
  | fail {r s} (c : PreparedWasmExhausted p tr t r pub s) :
      PreparedWasmExecution p tr t pub r s 1 c.final (some c.error)
  | advance {r s n final error} (c : PreparedWasmContinue p tr t r pub s)
      (tail : PreparedWasmExecution p tr t pub (r+1) c.next n final error) :
      PreparedWasmExecution p tr t pub r s (n+1) final error

/-- Actual fuelled interpreter and exit synchronization for the whole finite
certificate. Additional fuel is harmless once end or a trap is reached. -/
theorem prepared_wasm_execution_run (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (air : PreparedWasmAir table tr t pub) (cfg : NearCfg) (p : Prepared)
    {r : Nat} {s : St} {n : Nat} {final : St} {error : Option String}
    (execution : PreparedWasmExecution p tr t pub r s n final error)
    (context : PreparedWasmGasContext s) (extra : Nat) :
    ∃ raw,run cfg p (n+extra) s=(match error with | none => .fin raw | some e => .abort raw e) ∧
      sync raw=.ok final := by
  induction execution with
  | finish c =>
    have h:=prepared_wasm_end_certificate table tr t pub air cfg p _ _ c context
    refine ⟨c.raw,?_,h.2⟩
    rw [Nat.add_comm 1 extra,run,h.1]
  | fail c =>
    have h:=prepared_wasm_exhausted_certificate table tr t pub air cfg p _ _ c context
    refine ⟨c.final,?_,h.2⟩
    rw [Nat.add_comm 1 extra,run,h.1]
  | advance c tail ih =>
    have contextNext:=prepared_wasm_continue_gas table tr t pub air cfg p _ _ c context
    obtain ⟨raw,h,synced⟩:=ih contextNext
    refine ⟨raw,?_,synced⟩
    rw [Nat.add_right_comm _ 1 extra,run,(prepared_wasm_continue table tr t pub air cfg p _ _ c).1]
    exact h

/-- Boundary to actual `callEntry`. The `enter` premise is deliberately the
real prepared prologue after CallingWasm reset; its derivation from PREP and
initial public state is a separate obligation. -/
theorem prepared_wasm_execution_call_entry (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (air : PreparedWasmAir table tr t pub) (cfg : NearCfg) (p : Prepared)
    (host entered : St) (fi r n : Nat) (final : St) (error : Option String)
    (entry : enter p {host with
      gas := {host.gas with g:=host.gas.remaining}
      stack := #[]
      frames := []} fi=.cont entered)
    (execution : PreparedWasmExecution p tr t pub r entered n final error)
    (context : PreparedWasmGasContext entered) (extra : Nat) :
    callEntry cfg p (n+extra) host fi=.ok (final,error) := by
  obtain ⟨raw,runH,synced⟩:=prepared_wasm_execution_run table tr t pub air cfg p execution context extra
  simp only [callEntry,entry,runH]
  cases error <;> simp only [synced,Except.map]

end NearCompression
