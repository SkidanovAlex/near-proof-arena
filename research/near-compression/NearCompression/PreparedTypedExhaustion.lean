import NearCompression.PreparedTypedPadding
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
/-- On exhaustion, the AIR freezes the pre-trap payload while the actual
abort synchronizes failure gas. These are deliberately distinct states. -/
theorem prepared_typed_setup_exhaustion_snapshot (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
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
    tr.cell 0 (r+1) 41=1 ∧ tr.cell 0 (r+1) 42=1 ∧
    preparedExecWord64 (tr.cell 0 (r+1)) 299=s.gas.g ∧
    preparedCodeExecPC (tr.cell 0 (r+1))=f.pc ∧
    (∀i,i<9 → tr.cell 0 (r+1) (32+i)=if i=sp then 1 else 0) ∧
    preparedTypedStack (tr.cell 0 (r+1)) sp=s.stack ∧
    preparedTypedLocalArray (tr.cell 0 (r+1)) count=f.locals ∧
    PreparedControlLabels (tr.cell 0 (r+1)) f root := by
  have failure:=prepared_typed_setup_exhaustion codeCount count tr pub holds cfg bytes method ctx blockLevel eligible accepted
    r nonlast active s f fs sp root state fn context insufficient
  have localH:=prepared_typed_exec_local codeCount count tr pub holds
  have borrow:=prepared_control_gas_exhaustion _ tr 0 r pub (prepared_typed_gas_source count state.countBound) localH nonlast
    (by rw [←state.gas];exact insufficient)
  have quiet : preparedExecGasSuccess.eval tr 0 r pub=0 := by
    change ((1:Fp)+ -tr.cell 0 r 41)*((1:Fp)+ -tr.cell 0 r 430)=0
    rw [borrow.1];grind
  have control:=prepared_typed_quiet_pc_labels count state.countBound tr 0 r pub localH nonlast quiet
  refine ⟨failure.1,failure.2.1,failure.2.2.1,failure.2.2.2,control.1.trans state.pc.symm,
    prepared_typed_quiet_depth count state.countBound tr 0 r pub localH nonlast quiet sp state.depth state.selected,?_,?_,?_⟩
  · rw [state.stack]
    apply prepared_typed_stack_congr
    intro i hi
    exact prepared_typed_quiet_stack_value count state.countBound tr 0 r pub localH nonlast quiet i (by have h:=state.depth;omega)
  · exact (prepared_typed_quiet_local_array count state.countBound tr 0 r pub localH nonlast quiet).trans state.locals.symm
  · exact prepared_control_labels_transport _ _ f f root state.labels rfl control.2.1 control.2.2.1 control.2.2.2
end NearCompression
