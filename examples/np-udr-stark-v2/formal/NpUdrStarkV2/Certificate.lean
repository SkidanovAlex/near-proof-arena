import NpUdrStarkV2.Assembly

/-!
# `NpUdrStarkV2.certificate`

On the judge's **native-lean** route the certificate's type
`ArenaExpectedInst.expectedType` is generated *inside the judge* from its own
copy of the challenge and its own build outputs
(`spec/lean/judge/ExpectedV3D0.native-lean.lean.template`, spliced in a
generated `ArenaExpectedInst` module; see `NpUdrStarkV2/Assembly.lean`). It is
therefore not an importable module for the candidate.

This file instead

* fixes the public digest to `sha256 publicBin` (`publicDigest`, with the
  concrete D0a `params.bin` bytes pinned by a kernel check so any drift in
  `PublicBin.lean` is caught), and
* exposes `certificate`, `certificate_of` with the `pd`/`hpub` pair already
  discharged (`rfl`): the exact term the judge's
  `ArenaExpectedInst.expectedType` will be checked against, once the judge
  renders it with the D0a spec (`NearSpecV3.challengeSpecD0a` /
  `challengeParamsD0a`, as `nearV3_admission_with_extract_b` is stated).

`certificate` is still **conditional** on `ExtractV3Stmt`, `hcomp`(render) and
`halign`; those are the open obligations
(`docs/zk-formal/STATUS-V3-ASSEMBLY.md` §3) and the candidate is not yet
ADMITTED. No `sorry`, `axiom` or `native_decide`.
-/

namespace NpUdrStarkV2

open ArenaCore ZkFormal ZkFormal.Air ZkFormal.Prover ZkFormal.Size ZkFormal.V2 ZkFormal.Algebra
  ZkFormal.NearV3.Assembly NearSpecV3

local instance : ZkFormal.Prover.Np.G.AuxG := ⟨2, by decide⟩

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

/-- `certificate_of` with `pd := sha256 publicBin` discharged by `rfl`. This is
the shape of the judge's `ArenaExpectedInst.expectedType` (with the D0a spec);
it becomes closed once the open obligations land. -/
theorem certificate
    (hext : ExtractV3Stmt)
    (hintSel : WfClaim → List UInt8 → Hint)
    (hsplits : ∀ h π : List UInt8, split (join h π) = some (h, π))
    (traceOf : WfClaim → List UInt8 → Trace Fp)
    (hcomp : ∀ c w, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      ∃ cb', prepV3b (WfClaim.encode c) (Hint.encode (hintSel c w)) = some cb' ∧
        HoldsP nearAirV3 (Udr.pubOf Fp cb') (traceOf c w) ∧
        (ZkFormal.Prover.Np.G.VdP nearAirV3).headerOk
          (trHdr nearAirV3.toAir (traceOf c w)) = true)
    (halign : ∀ c w, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      RollAligned nearAirV3.toAir ZkFormal.Prover.Np.G.dp
        (trHdr nearAirV3.toAir (traceOf c w)))
    (hjoin : ∀ c w π, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      π.length ≤ v3MaxInner →
      (join (Hint.encode (hintSel c w)) π).length ≤ challengeParamsD0a.maxProofBytes)
    (bd : Digest) (tid : String) :
    AdmissionStatement challengeParamsD0a
      { publicDigest := publicDigest, impl := .nativeTrusted bd tid Model.verifier } :=
  certificate_of hext hintSel hsplits traceOf hcomp halign hjoin publicDigest bd tid rfl

end NpUdrStarkV2
