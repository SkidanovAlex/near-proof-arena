import ZkFormal.NearV3.Assembly.ExtractV3Proof
import ZkFormal.NearV3.Render.CompleteV3Chacha

/-!
# ZkFormal.NearV3.Assembly.AdmissionV3 — the D0a certificate

Soundness: `extractV3 : ExtractV3Stmt` (`ExtractV3Proof.lean`).  Completeness:
`completeV3_of_chacha : ChachaSideV3 → CompleteV3Stmt` (`Render/CompleteV3.lean`) with
`chachaSideV3 : ChachaSideV3`, i.e. `completeV3 : CompleteV3Stmt` (`Render/CompleteV3Chacha.lean`).
Combined through `nearV3_admission_of` (`RenderV3Bundle.lean`):

* **`nearV3_admission_final`** — the `AdmissionStatement` of `near-chunk-validation-d0-stark` from the
  implementation connection `himpl` alone (plus the public-digest binding `hpub`, as every route);

* **`nearV3_admission_of_chacha'`** — the `AdmissionStatement` of `near-chunk-validation-d0-stark`
  from `ChachaSideV3` and the implementation connection `himpl` only;
* `nearV3_admission_of_chacha''` — the same statement via `nearV3_admission_of_complete` (cross-check).

The last two are the intermediate forms (before `ChachaSideV3` was proved).
-/
set_option autoImplicit false
namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

/-- The deployed auxiliary-group parameter `g = 2` (as `NearAdmission` / `RenderV3Bundle`). -/
local instance auxG2_admissionV3 : ZkFormal.Prover.Np.G.AuxG := ⟨2, by decide⟩

/-- **The v3 admission certificate from the ChaCha side alone** (soundness `extractV3`, completeness
`completeV3_of_chacha`). -/
theorem nearV3_admission_of_chacha' (hch : ChachaSideV3)
    (art : ArenaCore.ArtifactDescription) (pub : List UInt8) (hpub : sha256 pub = art.publicDigest)
    (himpl : art.impl.Connection challengeParamsD0a.verifyFuel
      (ZkFormal.Prover.Np.G.npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier) :
    ArenaCore.AdmissionStatement challengeParamsD0a art :=
  nearV3_admission_of_chacha extractV3 hch art pub hpub himpl

/-- The same certificate via `nearV3_admission_of_complete` (cross-check: both routes agree on the
statement). -/
theorem nearV3_admission_of_chacha'' (hch : ChachaSideV3)
    (art : ArenaCore.ArtifactDescription) (pub : List UInt8) (hpub : sha256 pub = art.publicDigest)
    (himpl : art.impl.Connection challengeParamsD0a.verifyFuel
      (ZkFormal.Prover.Np.G.npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier) :
    ArenaCore.AdmissionStatement challengeParamsD0a art :=
  nearV3_admission_of_complete (completeV3_of_chacha hch) art pub hpub himpl

/-- **The v3 D0a admission certificate.** Soundness (`extractV3`) and completeness (`completeV3`)
are proved; the only premise is the implementation connection `himpl` of the artifact. -/
theorem nearV3_admission_final
    (art : ArenaCore.ArtifactDescription) (pub : List UInt8) (hpub : sha256 pub = art.publicDigest)
    (himpl : art.impl.Connection challengeParamsD0a.verifyFuel
      (ZkFormal.Prover.Np.G.npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier) :
    ArenaCore.AdmissionStatement challengeParamsD0a art :=
  nearV3_admission_of extractV3 completeV3 art pub hpub himpl

end ZkFormal.NearV3.Assembly
