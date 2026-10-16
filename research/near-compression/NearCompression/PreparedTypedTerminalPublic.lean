import NearCompression.PreparedTypedTerminal
import NearCompression.PreparedTypedPaddedExit
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

/-- Public failure output for an actual gas-exhaustion step, including arbitrary
padding. The public gas is the pretrap snapshot; it is deliberately not equated
to the interpreter's synchronized abort gas. -/
theorem prepared_typed_exhaustion_public_exit (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (counts : preparedExecBoundaryCountsCheck pub=true)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (s : St) (f : Frame) (fs : List Frame) (sp : Nat) (root : Label)
    (state : PreparedTypedState (tr.cell 0 r) s f fs sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (context : PreparedWasmGasContext s)
    (insufficient : s.gas.g<preparedExecWord64 (tr.cell 0 r) 502) :
    step cfg eligible.setup.program s=.abort {s with gas:=preparedWasmFailureGas s (preparedExecWord64 (tr.cell 0 r) 502)}
      (preparedWasmFailureError s (preparedExecWord64 (tr.cell 0 r) 502)) ∧
    pub.getD 68 0=1 ∧ pub.getD 69 0=1 ∧
    preparedTypedPublicGas pub true=s.gas.g := by
  obtain ⟨terminal,done,failed,gas⟩:=prepared_typed_setup_exhaustion codeCount count tr pub holds
    cfg bytes method ctx blockLevel eligible accepted r nonlast active s f fs sp root state fn context insufficient
  have output:=prepared_typed_done_public_exit codeCount count state.countBound tr pub holds counts
    (r+1) nonlast done
  exact ⟨terminal,output.1,output.2.1.trans failed,output.2.2.trans gas⟩

/-- Successful root return is linked to the actual public gas/status after
any padding suffix. This is the raw terminal step, before sync. -/
theorem prepared_typed_root_end_public_exit (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (counts : preparedExecBoundaryCountsCheck pub=true)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (r : Nat) (nonlast : r+1<tr.height 0) (active : tr.cell 0 r 41=0)
    (isEnd : tr.cell 0 r 469=1) (absent : tr.cell 0 r 639=0)
    (s : St) (f : Frame) (sp : Nat) (root : Label)
    (state : PreparedTypedState (tr.cell 0 r) s f [] sp count root)
    (fn : f.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
    (enough : preparedExecWord64 (tr.cell 0 r) 502≤s.gas.g) :
    sp=0 ∧ step cfg eligible.setup.program s=.fin {s with
      stack:=#[]
      frames:=[]
      stackRem:=s.stackRem+eligible.func.stackCharge
      gas:={s.gas with g:=preparedTypedPublicGas pub true}} ∧
    pub.getD 68 0=1 ∧ pub.getD 69 0=0 := by
  obtain ⟨depth,terminal,done,failed⟩:=prepared_typed_setup_root_end codeCount count tr pub holds
    cfg bytes method ctx blockLevel eligible accepted r nonlast active isEnd absent s f sp root state fn enough
  have output:=prepared_typed_done_public_exit codeCount count state.countBound tr pub holds counts
    (r+1) nonlast done
  refine ⟨depth,?_,output.1,output.2.1.trans failed⟩
  rw [output.2.2]
  exact terminal
end NearCompression
