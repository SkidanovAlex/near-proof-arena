import NearCompression.PreparedLocalsTerminal
import NearCompression.PreparedLocalsGasContext
import NearCompression.PreparedLocalsLegacyState
import NearCompression.PreparedLocalsBranchContinue
import NearCompression.PreparedLocalsAuthenticatedControl
import NearCompression.PreparedLocalsAuthenticatedState
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
structure PreparedLocalsTerminalWitness (cfg : NearCfg) (p : Prepared) (tr : Trace Fp) (pf : PFunc) (count : Nat) (root : Label) where
  row : Nat
  nonlast : row+1<tr.height 0
  before : St
  frame : Frame
  sp : Nat
  state : PreparedLocalsState (tr.cell 0 row) before frame [] sp count root
  func : p.funcs[frame.fn]?=some pf
  context : PreparedWasmGasContext before
  active : tr.cell 0 row 41=0
  raw : St
  final : St
  error : Option String
  terminal : step cfg p before=(match error with | none=>.fin raw | some e=>.abort raw e)
  synced : sync raw=.ok final
  done : tr.cell 0 (row+1) 41=1
  failed : tr.cell 0 (row+1) 42=if error.isSome then 1 else 0

def PreparedLocalsTerminalWitness.result {cfg p tr pf count root}
    (w : PreparedLocalsTerminalWitness cfg p tr pf count root) : Res :=
  match w.error with | none=>.fin w.raw | some e=>.abort w.raw e

theorem prepared_locals_active_nonlast (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr)
    (r : Nat) (hr : r<tr.height 0) (active : tr.cell 0 r 41=0) : r+1<tr.height 0 := by
  have localH:=prepared_locals_exec_local codeCount count tr pub holds
  have h:=localH.constr r hr preparedLocalsLiteralExec0997
    (prepared_locals_base_member count _ (List.getElem_mem (l:=preparedLocalsLiteralExecBase) (n:=997) (by decide)))
  change (if r+1=tr.height 0 then (1:Fp) else 0)*(tr.cell 0 r 41+ -(1:Fp))=0 at h
  by_cases last:r+1=tr.height 0
  · rw [if_pos last,active] at h
    have impossible : (1:Fp)=0:=by grind
    exact False.elim ((by decide : (1:Fp)≠0) impossible)
  · omega

/-- All supported opcodes compose into actual Wasm.run. Source preparation,
CODE authentication, local transitions and gas-context preservation are proved
interfaces, not an assumed per-step execution certificate. Entry-state binding
and public terminal-output propagation are separate obligations. -/
theorem prepared_locals_execution_run (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedLocalsLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedLocalsSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (fuel r : Nat) (s : St) (f : Frame) (sp : Nat) (root : Label)
    (hr : r<tr.height 0) (fuelEnough : tr.height 0-r≤fuel)
    (active : tr.cell 0 r 41=0) (state : PreparedLocalsState (tr.cell 0 r) s f [] sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (context : PreparedWasmGasContext s) :
    ∃ witness:PreparedLocalsTerminalWitness cfg eligible.setup.program tr eligible.func count root,
      r≤witness.row ∧ run cfg eligible.setup.program fuel s=witness.result := by
  induction fuel generalizing r s f sp with
  | zero => omega
  | succ fuel ih =>
    have nonlast:=prepared_locals_active_nonlast codeCount count tr pub holds r hr active
    have localH:=prepared_locals_exec_local codeCount count tr pub holds
    obtain ⟨setup,func,checked⟩:=prepared_locals_setup_checked count cfg bytes method ctx pub blockLevel eligible accepted
    have actualFunc : eligible.setup.program.funcs[f.fn]?=some eligible.func := by rw [fn];exact func
    by_cases enough:preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g
    · have advanceCase
          (continuation : ∃ next f' sp',step cfg eligible.setup.program s=.cont next ∧
            PreparedLocalsState (tr.cell 0 (r+1)) next f' [] sp' count root ∧
            f'.fn=f.fn ∧ tr.cell 0 (r+1) 41=0 ∧ tr.cell 0 (r+1) 42=0) :
          ∃ witness:PreparedLocalsTerminalWitness cfg eligible.setup.program tr eligible.func count root,
            r≤witness.row ∧ run cfg eligible.setup.program (fuel+1) s=witness.result := by
        obtain ⟨next,f',sp',stepNext,post,fnEq,nextActive,_⟩:=continuation
        have nextContext:=(prepared_locals_setup_continue_context codeCount count tr pub holds cfg bytes method ctx blockLevel eligible accepted
          r hr s next f [] sp state.1.1 fn enough context stepNext).2
        obtain ⟨witness,after,executed⟩:=ih (r+1) next f' sp' nonlast (by omega) nextActive post (fnEq.trans fn) nextContext
        refine ⟨witness,by omega,?_⟩
        rw [run,stepNext];exact executed
      obtain ⟨tag,tagBound,ops⟩:=prepared_locals_opcode_selected count tr 0 r pub localH hr
      have tags : tag=0 ∨ tag=1 ∨ tag=2 ∨ tag=3 ∨ tag=4 ∨ tag=5 ∨ tag=6 ∨ tag=7 ∨ tag=8:=by omega
      rcases tags with eq|eq|eq|eq|eq|eq|eq|eq|eq <;> subst tag
      · apply advanceCase
        obtain ⟨next,stepNext,post,done,failed⟩:=prepared_locals_setup_stack_state true codeCount count tr pub holds
          cfg bytes method ctx blockLevel eligible accepted r nonlast active (ops 0 (by decide)) s f [] sp root state fn enough
        exact ⟨next,_,_,stepNext,post,rfl,done,failed⟩
      · apply advanceCase
        obtain ⟨next,stepNext,post,done,failed⟩:=prepared_locals_setup_add_state codeCount count tr pub holds
          cfg bytes method ctx blockLevel eligible accepted r nonlast active (ops 1 (by decide)) s f [] sp root state fn enough
        exact ⟨next,_,_,stepNext,post,rfl,done,failed⟩
      · apply advanceCase
        obtain ⟨next,stepNext,post,done,failed⟩:=prepared_locals_setup_stack_state false codeCount count tr pub holds
          cfg bytes method ctx blockLevel eligible accepted r nonlast active (ops 2 (by decide)) s f [] sp root state fn enough
        exact ⟨next,_,_,stepNext,post,rfl,done,failed⟩
      · have isEnd : tr.cell 0 r 469=1:=ops 3 (by decide)
        by_cases absent:tr.cell 0 r 639=0
        · obtain ⟨_,terminal,done,failed⟩:=prepared_locals_setup_root_end codeCount count tr pub holds
            cfg bytes method ctx blockLevel eligible accepted r nonlast active isEnd absent s f sp root state fn enough
          have enoughRow : preparedExecWord64 (tr.cell 0 r) 502≤preparedExecWord64 (tr.cell 0 r) 299 := by rw [←state.1.1.gas];exact enough
          have gasNext:=(prepared_control_gas_success _ tr 0 r pub (prepared_locals_gas_source count) localH nonlast active enoughRow).2
          let raw : St := {s with
            stack:=#[]
            frames:=[]
            stackRem:=s.stackRem+eligible.func.stackCharge
            gas:={s.gas with g:=preparedExecWord64 (tr.cell 0 (r+1)) 299}}
          let final : St := {raw with gas:={raw.gas with burnt:=s.gas.prepaid-preparedExecWord64 (tr.cell 0 (r+1)) 299}}
          have synced : sync raw=.ok final := by
            have h:=prepared_wasm_end_sync s eligible.func (preparedExecWord64 (tr.cell 0 r) 502) context
            simpa only [raw,final,gasNext,←state.1.1.gas] using h
          let witness : PreparedLocalsTerminalWitness cfg eligible.setup.program tr eligible.func count root :=
            ⟨r,nonlast,s,f,sp,state,actualFunc,context,active,raw,final,none,terminal,synced,done,failed⟩
          refine ⟨witness,Nat.le_refl _,?_⟩
          rw [run,terminal];rfl
        · have nested : tr.cell 0 r 639=1 := by
            rcases state.1.2 with h|⟨_,_,one,_,_⟩
            · exact False.elim (absent h.1)
            · exact one
          apply advanceCase
          obtain ⟨next,stepNext,post,done,failed⟩:=prepared_locals_setup_nested_end_state codeCount count tr pub holds
            cfg bytes method ctx blockLevel eligible accepted r nonlast active isEnd nested s f [] sp root state fn enough
          exact ⟨next,_,_,stepNext,post,rfl,done,failed⟩
      · apply advanceCase
        obtain ⟨e,next,_,stepNext,post,done,failed⟩:=prepared_locals_setup_block_state codeCount count tr pub holds
          cfg bytes method ctx blockLevel eligible accepted r nonlast active (ops 4 (by decide)) s f [] sp root state fn enough
        exact ⟨next,_,_,stepNext,post,rfl,done,failed⟩
      · apply advanceCase
        exact prepared_locals_setup_branch_continue codeCount count tr pub holds cfg bytes method ctx blockLevel eligible accepted
          r nonlast active (ops 5 (by decide)) s f [] sp root state fn enough
      · apply advanceCase
        obtain ⟨next,stepNext,post,done,failed⟩:=prepared_locals_setup_success_state codeCount count tr pub holds
          cfg bytes method ctx blockLevel eligible accepted r nonlast active .get (ops 6 (by decide))
          s f [] sp root state fn enough
        exact ⟨next,_,_,stepNext,post,rfl,done,failed⟩
      · apply advanceCase
        obtain ⟨next,stepNext,post,done,failed⟩:=prepared_locals_setup_success_state codeCount count tr pub holds
          cfg bytes method ctx blockLevel eligible accepted r nonlast active .set (ops 7 (by decide))
          s f [] sp root state fn enough
        exact ⟨next,_,_,stepNext,post,rfl,done,failed⟩
      · apply advanceCase
        obtain ⟨next,stepNext,post,done,failed⟩:=prepared_locals_setup_success_state codeCount count tr pub holds
          cfg bytes method ctx blockLevel eligible accepted r nonlast active .tee (ops 8 (by decide))
          s f [] sp root state fn enough
        exact ⟨next,_,_,stepNext,post,rfl,done,failed⟩
    · have insufficient:s.gas.g<preparedExecWord64 (tr.cell 0 r) 502:=by omega
      obtain ⟨terminal,done,failed,_⟩:=prepared_locals_setup_exhaustion codeCount count tr pub holds
        cfg bytes method ctx blockLevel eligible accepted r nonlast active s f [] sp root state fn context insufficient
      let raw : St:={s with gas:=preparedWasmFailureGas s (preparedExecWord64 (tr.cell 0 r) 502)}
      let err:=preparedWasmFailureError s (preparedExecWord64 (tr.cell 0 r) 502)
      have synced : sync raw=.ok raw:=prepared_wasm_failure_sync s _ context
      let witness : PreparedLocalsTerminalWitness cfg eligible.setup.program tr eligible.func count root :=
        ⟨r,nonlast,s,f,sp,state,actualFunc,context,active,raw,raw,some err,terminal,synced,done,failed⟩
      refine ⟨witness,Nat.le_refl _,?_⟩
      rw [run,terminal];rfl

end NearCompression
