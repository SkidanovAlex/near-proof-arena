import NearCompression.PreparedTypedTerminalStack
import NearCompression.PreparedTypedTerminalWitness
import NearCompression.PreparedTypedExecutionShape
namespace NearCompression
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

private theorem abort_stack (s t : St) (e f : String) (h : Res.abort s e=Res.abort t f) : s.stack=t.stack :=
  congrArg St.stack (Res.abort.inj h).1

/-- Every concrete terminal witness publishes the actual synchronized stack.
Failure preserves the pretrap stack; a successful root return empties it. -/
theorem prepared_typed_witness_stack (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (counts : preparedExecBoundaryCountsCheck pub=true)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (root : Label)
    (w : PreparedTypedTerminalWitness cfg eligible.setup.program tr eligible.func count root)
    (fn : w.frame.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size) :
    preparedTypedPublicStack pub=w.final.stack := by
  have finalStack:=prepared_typed_sync_stack w.raw w.final w.synced
  rw [finalStack]
  have localH:=prepared_typed_exec_local codeCount count tr pub holds
  by_cases enough:preparedExecWord64 (tr.cell 0 w.row) 502≤w.before.gas.g
  · have enoughRow : preparedExecWord64 (tr.cell 0 w.row) 502≤preparedExecWord64 (tr.cell 0 w.row) 299 := by
      rw [←w.state.gas];exact enough
    have borrow:=(prepared_control_gas_success _ tr 0 w.row pub
      (prepared_typed_gas_source count w.state.countBound) localH w.nonlast w.active enoughRow).1
    have flag:=(prepared_typed_terminal_flags count w.state.countBound tr 0 w.row pub localH w.nonlast w.active).2.2
    rw [w.done,borrow,w.active] at flag
    obtain ⟨tag,bound,hot⟩:=prepared_typed_opcode_total count w.state.countBound tr 0 w.row pub localH (by have h:=w.nonlast;omega)
    have endBit:=hot 3 (by decide)
    change tr.cell 0 w.row 469=(if 3=tag then 1 else 0) at endBit
    have isEnd : tr.cell 0 w.row 469=1 := by
      by_cases eq:3=tag
      · simpa only [eq,ite_true] using endBit
      · rw [ite_eq_right eq] at endBit
        rw [endBit] at flag
        have impossible : (1:Fp)=0:=by grind
        exact False.elim ((by decide : (1:Fp)≠0) impossible)
    have absent : tr.cell 0 w.row 639=0 := by rw [isEnd] at flag;grind
    have published:=prepared_typed_root_end_public_stack codeCount count tr pub holds counts cfg bytes method ctx blockLevel
      eligible accepted w.row w.nonlast w.active isEnd absent w.before w.frame w.sp root w.state fn enough
    obtain ⟨_,terminal,_,_⟩:=prepared_typed_setup_root_end codeCount count tr pub holds cfg bytes method ctx blockLevel
      eligible accepted w.row w.nonlast w.active isEnd absent w.before w.frame w.sp root w.state fn enough
    have same:=w.terminal
    rw [terminal] at same
    cases error:w.error <;> simp only [error] at same
    · injection same with rawEq
      exact published.2.trans (congrArg St.stack rawEq)
    · cases same
  · have insufficient : w.before.gas.g<preparedExecWord64 (tr.cell 0 w.row) 502:=by omega
    have published:=prepared_typed_exhaustion_public_stack codeCount count tr pub holds counts cfg bytes method ctx blockLevel
      eligible accepted w.row w.nonlast w.active w.before w.frame [] w.sp root w.state fn w.context insufficient
    have terminal:=(prepared_typed_setup_exhaustion codeCount count tr pub holds cfg bytes method ctx blockLevel
      eligible accepted w.row w.nonlast w.active w.before w.frame [] w.sp root w.state fn w.context insufficient).1
    have same:=w.terminal
    rw [terminal] at same
    cases error:w.error <;> simp only [error] at same
    · cases same
    · rename_i err
      have stackEq : w.before.stack=w.raw.stack := abort_stack
        {w.before with gas:=preparedWasmFailureGas w.before (preparedExecWord64 (tr.cell 0 w.row) 502)}
        w.raw (preparedWasmFailureError w.before (preparedExecWord64 (tr.cell 0 w.row) 502)) err same
      exact published.2.trans stackEq
end NearCompression
