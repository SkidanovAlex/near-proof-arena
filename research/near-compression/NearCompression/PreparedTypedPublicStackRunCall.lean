import NearCompression.PreparedTypedPublicRunCall
import NearCompression.PreparedTypedWitnessStack
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.Wasm

/-- Actual typed runCall, public status/gas snapshot, and exact final stack.
Verifier-side preparation and bounded profile assumptions remain explicit. -/
theorem prepared_typed_public_stack_run_call (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedRunCallCheck count cfg code method ctx pub blockLevel=some eligible)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel) :
    ∃w:PreparedTypedTerminalWitness cfg eligible.setup.program tr eligible.func count (preparedControlRootLabel eligible.func),
      w.frame.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size ∧
      runCall cfg code method ctx fuel blockLevel full none=.done w.final w.error ∧
      PreparedTypedWitnessPublished pub w ∧ preparedTypedPublicStack pub=w.final.stack := by
  obtain ⟨codeCheck,entry⟩:=prepared_typed_run_call_checked count cfg code method ctx pub blockLevel eligible accepted
  have counts : preparedExecBoundaryCountsCheck pub=true := by
    simp only [preparedExecEntryCheck,Bool.and_eq_true] at entry
    exact entry.1
  obtain ⟨w,indexEq,actual,published⟩:=prepared_typed_public_run_call codeCount count tr pub holds cfg code method ctx blockLevel full eligible accepted fuel enoughFuel
  exact ⟨w,indexEq,actual,published,prepared_typed_witness_stack codeCount count tr pub holds counts cfg code method ctx blockLevel
    eligible codeCheck (preparedControlRootLabel eligible.func) w indexEq⟩
end NearCompression
