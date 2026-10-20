import NearCompression.PreparedTypedPublicStack
import NearCompression.PreparedTypedTerminalPublic
import NearCompression.PreparedTypedExhaustion
import NearCompression.PreparedTypedFrameDepth
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

/-- Synchronization changes gas accounting only, including the failure path. -/
theorem prepared_typed_sync_stack (s final : St) (synced : sync s=.ok final) :
    final.stack=s.stack := by
  simp only [sync] at synced
  split at synced
  · cases synced; rfl
  · split at synced
    · cases synced; rfl
    · cases synced

/-- The public failure stack is exactly the pretrap stack, including mixed tags.
This does not identify the public gas snapshot with synchronized gas accounting. -/
theorem prepared_typed_exhaustion_public_stack (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
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
    (pub.getD 67 0).toNat=sp ∧ preparedTypedPublicStack pub=s.stack := by
  obtain ⟨_,done,_,_,_,selected,stack,_,_⟩:=prepared_typed_setup_exhaustion_snapshot
    codeCount count tr pub holds cfg bytes method ctx blockLevel eligible accepted
    r nonlast active s f fs sp root state fn context insufficient
  have bound:=prepared_typed_done_public_stack codeCount count state.countBound tr pub holds counts
    (r+1) nonlast done sp state.depth selected
  exact ⟨bound.1,bound.2.trans stack⟩

/-- A successful outer return publishes the empty stack. Depth preservation is
proved from the end opcode's actual literal constraints. -/
theorem prepared_typed_root_end_public_stack (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
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
    (pub.getD 67 0).toNat=0 ∧ preparedTypedPublicStack pub=#[] := by
  obtain ⟨depth,_,done,_⟩:=prepared_typed_setup_root_end codeCount count tr pub holds
    cfg bytes method ctx blockLevel eligible accepted r nonlast active isEnd absent s f sp root state fn enough
  have selected:=prepared_typed_frame_depth count state.countBound tr 0 r pub
    (prepared_typed_exec_local codeCount count tr pub holds) nonlast 3 (Or.inl rfl)
    isEnd sp state.depth state.selected
  have bound:=prepared_typed_done_public_stack codeCount count state.countBound tr pub holds counts
    (r+1) nonlast done sp state.depth selected
  rw [depth] at bound
  exact ⟨bound.1,by simpa [preparedTypedStack] using bound.2⟩
end NearCompression
