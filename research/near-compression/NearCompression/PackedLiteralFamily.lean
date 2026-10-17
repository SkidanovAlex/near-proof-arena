import NearCompression.PackedLiteralExecution
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.Wasm

/-- Public code-table capacity varies; instruction constraints and packing do not. -/
def packedCandidateAirFor (codeLength : Nat) : AirP :=
  {packedCandidateAir with numPub:=66+25*codeLength,maxPub:=66+25*codeLength}

theorem packed_candidate_original_fixture : packedCandidateAirFor 193=packedCandidateAir := rfl

/-- The closed structural proof is uniform in public CODE length. This does not
remove eligibility's supported-instruction, stack or execution-shape limits. -/
def packedLiteralFamilyCertificate (count : Nat) :
    PackedAirRefinement (preparedLiteralAir count) (packedCandidateAirFor count) packedLiteralLayouts where
  originalShape := packedLiteralCertificate.originalShape
  packedShape := packedLiteralCertificate.packedShape
  publicSegments := packedLiteralCertificate.publicSegments
  publicMaximum := rfl
  rangeSource := {
    noPublic := packedLiteralCertificate.rangeSource.noPublic
    receiver := packedLiteralCertificate.rangeSource.receiver
    constraints := packedLiteralCertificate.rangeSource.constraints }
  consistent := packedLiteralCertificate.consistent
  maxLog := packedLiteralCertificate.maxLog
  coverage := packedLiteralCertificate.coverage
  retained := packedLiteralCertificate.retained
  extra := packedLiteralCertificate.extra
  splitInteractions := packedLiteralCertificate.splitInteractions
  pairings := packedLiteralCertificate.pairings
  extraRange := packedLiteralCertificate.extraRange
  rangeTableOnly := packedLiteralCertificate.rangeTableOnly
  oldNoRange := packedLiteralCertificate.oldNoRange
  senders := packedLiteralCertificate.senders

theorem packed_literal_family_holds (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (packedCandidateAirFor count) pub tr) :
    HoldsP (preparedLiteralAir count) pub (packedLiftTrace packedLiteralLayouts tr) :=
  packed_holds_refinement _ _ _ (packedLiteralFamilyCertificate count) tr pub holds

theorem packed_literal_family_public_run_call (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (packedCandidateAirFor count) pub tr)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedLiteralRunCallCheck cfg code method ctx pub blockLevel=some eligible)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel) :
    ∃ witness:PreparedExecTerminalWitness cfg eligible.setup.program
        (packedLiftTrace packedLiteralLayouts tr) eligible.func,
      runCall cfg code method ctx fuel blockLevel full none=.done witness.final witness.error ∧
      PreparedExecPublishedOutput pub witness.final witness.error :=
  prepared_literal_public_run_call count (packedLiftTrace packedLiteralLayouts tr) pub
    (packed_literal_family_holds count tr pub holds) cfg code method ctx blockLevel full eligible accepted fuel enoughFuel

end NearCompression
