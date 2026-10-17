import NearCompression.PreparedExecContinue

namespace NearCompression
set_option maxRecDepth 65536
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

/-- A terminal witness retains the actual state immediately before the
terminal instruction, so later public-boundary proofs can use its row binding.
It is constructed from AIR below; no step-certificate premise is assumed. -/
structure PreparedExecTerminalWitness (cfg : NearCfg) (p : Prepared) (tr : Trace Fp) (pf : PFunc) where
  row : Nat
  nonlast : row+1<tr.height 0
  before : St
  frame : Frame
  sp : Nat
  state : PreparedExecState (tr.cell 0 row) before frame [] sp
  func : p.funcs[frame.fn]?=some pf
  context : PreparedWasmGasContext before
  labels : frame.labels=[] ∨ ∃ lab,frame.labels=[lab]
  active : tr.cell 0 row 41=0
  raw : St
  final : St
  error : Option String
  terminal : step cfg p before=(match error with | none=>.fin raw | some e=>.abort raw e)
  synced : sync raw=.ok final
  done : tr.cell 0 (row+1) 41=1
  failed : tr.cell 0 (row+1) 42=if error.isSome then 1 else 0

def PreparedExecTerminalWitness.result {cfg p tr pf} (w : PreparedExecTerminalWitness cfg p tr pf) : Res :=
  match w.error with | none=>.fin w.raw | some e=>.abort w.raw e

theorem prepared_literal_active_nonlast (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLiteralAir count) pub tr)
    (r : Nat) (hr : r<tr.height 0) (active : tr.cell 0 r 41=0) : r+1<tr.height 0 := by
  have localH:=prepared_exec_table_local _ _ _ count tr pub holds
  have member : preparedLiteralExec0642∈preparedLiteralExec :=
    List.getElem_mem (l:=preparedLiteralExec) (n:=642) (by decide)
  have h:=localH.constr r hr _ member
  change (if r+1=tr.height 0 then (1:Fp) else 0)*(tr.cell 0 r 41+ -(1:Fp))=0 at h
  by_cases last : r+1=tr.height 0
  · rw [ite_eq_left last,active] at h
    have impossible : (1:Fp)=0 := by grind
    exact False.elim ((by decide : (1:Fp)≠0) impossible)
  · omega

/-- Every active execution admitted by the literal tables terminates within
its remaining row budget. Successful continuations and terminal cases are
proved from the AIR and authenticated prepared code, not assumed transitions.
The conclusion includes actual Wasm.run and actual exit synchronization. -/
theorem prepared_literal_execution_run (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLiteralAir count) pub tr)
    (pf : PFunc) (fn : Nat) (checked : preparedCodeVariableCheck pf fn pub=true)
    (cfg : NearCfg) (p : Prepared) (fuel r : Nat) (s : St) (f : Frame) (sp : Nat)
    (hr : r<tr.height 0) (fuelEnough : tr.height 0-r≤fuel)
    (active : tr.cell 0 r 41=0) (state : PreparedExecState (tr.cell 0 r) s f [] sp)
    (func : p.funcs[f.fn]?=some pf) (context : PreparedWasmGasContext s)
    (labels : f.labels=[] ∨ ∃ lab,f.labels=[lab]) :
    ∃ witness:PreparedExecTerminalWitness cfg p tr pf,
      r≤witness.row ∧ run cfg p fuel s=witness.result := by
  induction fuel generalizing r s f sp with
  | zero => omega
  | succ fuel ih =>
    have nonlast:=prepared_literal_active_nonlast count tr pub holds r hr active
    have localH:=prepared_exec_table_local _ _ _ count tr pub holds
    by_cases enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g
    · have advanceCase (op : Option Bool) (selected : tr.cell 0 r (466+preparedWasmOpTag op)=1) :
          ∃ witness:PreparedExecTerminalWitness cfg p tr pf,
            r≤witness.row ∧ run cfg p (fuel+1) s=witness.result := by
        obtain ⟨next,stepNext,post,nextContext,nextActive,_⟩:=prepared_literal_continue op count tr pub holds
          pf fn checked r nonlast active selected cfg p s f [] sp state func context enough
        obtain ⟨witness,after,executed⟩:=ih (r+1) next
          {f with pc:=preparedCodeExecPC (tr.cell 0 (r+1))} (preparedWasmNextSP op sp)
          nonlast (by omega) nextActive post func nextContext labels
        refine ⟨witness,by omega,?_⟩
        rw [run,stepNext]
        exact executed
      obtain ⟨op,code,ops⟩:=prepared_exec_authenticated_opcode _ _ _ count tr pub holds
        prepared_literal_code_order prepared_literal_code_inactive pf fn checked r hr
      cases op with
      | constant value =>
        apply advanceCase (some true)
        exact ops 0 (by decide)
      | add =>
        apply advanceCase none
        exact ops 1 (by decide)
      | drop =>
        apply advanceCase (some false)
        exact ops 2 (by decide)
      | end_ =>
        have isEnd : tr.cell 0 r 469=1:=ops 3 (by decide)
        obtain ⟨empty,terminal,done,failed⟩:=prepared_exec_authenticated_end _ _ _ count tr pub holds
          prepared_literal_code_order prepared_literal_code_inactive prepared_literal_exec_closure
          prepared_literal_exec_gas prepared_literal_exec_end_guard pf fn checked r nonlast active isEnd
          cfg p s f sp state func labels enough
        have enoughRow : preparedExecWord64 (tr.cell 0 r) 502≤preparedExecWord64 (tr.cell 0 r) 299 := by
          rw [←state.gas];exact enough
        have gasNext:=(prepared_exec_gas_success _ tr 0 r pub prepared_literal_exec_gas localH nonlast active enoughRow).2
        let raw : St := {s with
          stack:=#[]
          frames:=[]
          stackRem:=s.stackRem+pf.stackCharge
          gas:={s.gas with g:=preparedExecWord64 (tr.cell 0 (r+1)) 299}}
        let final : St := {raw with gas:={raw.gas with burnt:=s.gas.prepaid-preparedExecWord64 (tr.cell 0 (r+1)) 299}}
        have synced : sync raw=.ok final := by
          have h:=prepared_wasm_end_sync s pf (preparedExecWord64 (tr.cell 0 r) 502) context
          simpa only [raw,final,gasNext,←state.gas] using h
        let witness : PreparedExecTerminalWitness cfg p tr pf :=
          ⟨r,nonlast,s,f,sp,state,func,context,labels,active,raw,final,none,terminal,synced,done,failed⟩
        refine ⟨witness,Nat.le_refl _,?_⟩
        rw [run,terminal]
        rfl
    · have insufficient : s.gas.g<preparedExecWord64 (tr.cell 0 r) 502:=by omega
      obtain ⟨terminal,done,failed,frozen⟩:=prepared_exec_authenticated_exhaustion _ _ _ count tr pub holds
        prepared_literal_code_order prepared_literal_code_inactive prepared_literal_exec_closure
        prepared_literal_exec_gas pf fn checked r nonlast active cfg p s f [] sp state func context insufficient
      let raw : St := {s with gas:=preparedWasmFailureGas s (preparedExecWord64 (tr.cell 0 r) 502)}
      let err := preparedWasmFailureError s (preparedExecWord64 (tr.cell 0 r) 502)
      have synced : sync raw=.ok raw:=prepared_wasm_failure_sync s _ context
      let witness : PreparedExecTerminalWitness cfg p tr pf :=
        ⟨r,nonlast,s,f,sp,state,func,context,labels,active,raw,raw,some err,terminal,synced,done,failed⟩
      refine ⟨witness,Nat.le_refl _,?_⟩
      rw [run,terminal]
      rfl

end NearCompression
