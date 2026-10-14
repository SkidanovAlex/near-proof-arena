import ZkFormal.NearV3.Assembly.NearAdmissionDefs
import ZkFormal.NearV3.D1.NearAirD1Defs
import ZkFormal.NearV3.D1.PrepD1
import ZkFormal.V2.PG.AdmissionDefs
import NearSpecV3.ChallengeD1a

/-!
# `ZkFormal.NearV3.D1.VerifierD1Defs` — the D1a verifier model (candidate side, phase 1)

Definitions only (verifier-model import rule).  The D1a analogue of `NpUdrStarkV2.Model.verifier`:

  `npVerifierP challengeSpecD1a nearAirV3D1 split prepD1b`

with the D0a wire split (`readBorshBytes`: `proof = borshBytes (HintD1.encode h) ‖ π`) and the
native preparation `prepD1b = decodeHintD1 ⋙ prepD1 ⋙ preparedBytesD1 · 0` (tapes of `P` or
more bytes rejected, as `prepV3`).  Not a certificate: the admission statement
(`AdmissionStatement (challengeParamsChunk .d1a) …`) is phase 3.
-/

namespace ZkFormal.NearV3.D1

/-- `decodeHintD1 ⋙ prepD1 ⋙ preparedBytesD1 · 0`, tapes below `P`. -/
def prepD1b (cb hb : List UInt8) : Option (List UInt8) :=
  match preparedTapeD1 cb hb with
  | .ok b => if b.length < ZkFormal.Algebra.P then some b else none
  | .error _ => none

end ZkFormal.NearV3.D1
