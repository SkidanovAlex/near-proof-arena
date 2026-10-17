import NearCompression.PreparedTypedRunCall
import NearCompression.PreparedTypedWitnessPublic
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.Wasm

/-- Actual runCall outcome and authenticated public status/gas snapshot for the
bounded typed profile. This does not identify every public stack field or prove
PREP inside AIR; setup is still computed by the verifier-side checker. -/
theorem prepared_typed_public_run_call (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedRunCallCheck count cfg code method ctx pub blockLevel=some eligible)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel) :
    ∃w:PreparedTypedTerminalWitness cfg eligible.setup.program tr eligible.func count (preparedControlRootLabel eligible.func),
      w.frame.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size ∧
      runCall cfg code method ctx fuel blockLevel full none=.done w.final w.error ∧
      PreparedTypedWitnessPublished pub w := by
  obtain ⟨codeCheck,entry⟩:=prepared_typed_run_call_checked count cfg code method ctx pub blockLevel eligible accepted
  have counts : preparedExecBoundaryCountsCheck pub=true := by
    simp only [preparedExecEntryCheck,Bool.and_eq_true] at entry
    exact entry.1
  obtain ⟨w,indexEq,actual⟩:=prepared_typed_run_call_indexed codeCount count tr pub holds cfg code method ctx blockLevel full eligible accepted fuel enoughFuel
  exact ⟨w,indexEq,actual,prepared_typed_witness_published codeCount count tr pub holds counts cfg eligible.setup.program eligible.func
    (preparedControlRootLabel eligible.func) w⟩
end NearCompression
