import NearCompression.PackedLiteralCertificate
import NearCompression.PreparedExecFinalRow

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.Wasm

/-- The actual packed AIR refines the authenticated Wasm runCall result.
The statement is conditional on semantic HoldsP and the existing preparation/
eligibility checker; native cryptographic acceptance is a separate obligation.
The supported slice remains one straight-line function and eight live i32 slots. -/
theorem packed_literal_public_run_call (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP packedCandidateAir pub tr)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedLiteralRunCallCheck cfg code method ctx pub blockLevel=some eligible)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel) :
    ∃ witness:PreparedExecTerminalWitness cfg eligible.setup.program
        (packedLiftTrace packedLiteralLayouts tr) eligible.func,
      runCall cfg code method ctx fuel blockLevel full none=.done witness.final witness.error ∧
      PreparedExecPublishedOutput pub witness.final witness.error :=
  prepared_literal_public_run_call 193 (packedLiftTrace packedLiteralLayouts tr) pub
    (packed_literal_holds tr pub holds) cfg code method ctx blockLevel full eligible accepted fuel enoughFuel

end NearCompression
