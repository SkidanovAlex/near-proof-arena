import NpUdrStarkV2.Model
import NpUdrStarkV2.PublicBin
import ZkFormal.NearV3.Assembly.AdmissionV3

/-!
# `NpUdrStarkV2.certificate`

On the judge's **native-lean** route the certificate's type
`ArenaExpectedInst.expectedType` is generated *inside the judge* from its own
copy of the challenge and its own build outputs
(`spec/lean/judge/ExpectedV3D0.native-lean.lean.template`, spliced in a
generated `ArenaExpectedInst` module; see `NpUdrStarkV2/Assembly.lean`). It is
therefore not an importable module for the candidate.

This file

* fixes the public digest to `sha256 publicBin` (`publicDigest`, with the
  concrete D0a `params.bin` bytes pinned by a kernel check so any drift in
  `PublicBin.lean` is caught), and
* proves `certificate`: the admission statement of the D0a challenge
  (`NearSpecV3.challengeParamsD0a`) for the artifact
  `{ publicDigest := sha256 publicBin, impl := .nativeTrusted bd tid Model.verifier }`,
  **unconditionally**.  It is main's `ZkFormal.NearV3.Assembly.nearV3_admission_final`
  (soundness `extractV3 : ExtractV3Stmt` and completeness `completeV3 : CompleteV3Stmt` both
  proved) with its two premises discharged: `hpub` by `rfl` (the digest is defined as
  `sha256 publicBin`) and `himpl` by `rfl` (`VerifierImpl.Connection _ _ v` is `v = m` on the
  `nativeTrusted` route, `formal-core/ArenaCore/Admission.lean`, and `Model.verifier` *is*
  `(npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier`).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only (`#print axioms` below and the guarded
audit `zk-formal/test/AuditAdmissionV3.lean`).  No `sorry`, `axiom` or `native_decide`.

The earlier conditional form (`NpUdrStarkV2.certificate_of`, `Assembly.lean`) is kept for
reference; the candidate's certificate no longer depends on it.
-/

namespace NpUdrStarkV2

open ArenaCore ZkFormal NearSpecV3

/-- `sha256 publicBin`, the `publicDigest` of the admission statement. -/
def publicDigest : Digest := sha256 publicBin

/-- The D0a `params.bin` digest recorded in `PublicBin.lean`
(`spec/tools/params_bin_v3.py <out> D0a`), checked by the kernel so the public
tape cannot silently change. -/
theorem publicDigest_eq :
    publicDigest =
      [0xab, 0x13, 0xc1, 0x99, 0x70, 0x99, 0x6e, 0xbe, 0x01, 0xbc, 0x3d, 0x92, 0x34, 0xf6, 0x4a, 0x1a,
       0x6a, 0x98, 0x97, 0x15, 0xf8, 0xda, 0x8d, 0xd7, 0xf9, 0x2e, 0x5a, 0xb5, 0xea, 0xc8, 0x95, 0x7f] := by
  decide +kernel

-- The default `maxRecDepth` (512) is exceeded while elaborating the application against the
-- expected artifact (a resource limit of the elaborator, not a logical option).
set_option maxRecDepth 20000

/-- **The D0a admission certificate of `np-udr-stark-v2`** (unconditional): the shape of the
judge's `ArenaExpectedInst.expectedType` with the D0a spec, for every build digest `bd` and
target id `tid`. -/
theorem certificate (bd : Digest) (tid : String) :
    AdmissionStatement challengeParamsD0a
      { publicDigest := publicDigest, impl := .nativeTrusted bd tid Model.verifier } :=
  ZkFormal.NearV3.Assembly.nearV3_admission_final
    { publicDigest := publicDigest, impl := .nativeTrusted bd tid Model.verifier }
    publicBin rfl rfl

end NpUdrStarkV2

/-- info: 'NpUdrStarkV2.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms NpUdrStarkV2.certificate
