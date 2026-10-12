import NpUdrStarkV2.Model
import NpUdrStarkV2.PublicBin
import ZkFormal.NearV3.Assembly.NearAdmission

/-!
# `NpUdrStarkV2.certificate_of`: the D0a admission statement from the open obligations

The judge renders `ArenaExpected.expectedTypeFor model` for this candidate as

```
AdmissionStatement
  (NearSpecV3.challengeParamsD0a)
  { publicDigest := pd, impl := .nativeTrusted bd tid NpUdrStarkV2.Model.verifier }
```

(the D0a challenge `near-chunk-validation-d0-stark`, statement
`near/pv86/chunk-validation/v0#D0a`, profile `validity-classical-128`,
`maxProofBytes = 8388608`, `verifyFuel = 2^30`; see
`spec/lean/judge/ExpectedV3D0.native-lean.lean.template` and
`NearSpecV3.challengeParamsD0a`).

`certificate_of` **is** `ZkFormal.NearV3.Assembly.nearV3_admission_with_extract_b`
specialised to this model and the concrete wire codecs. It is therefore a
**conditional** certificate: it proves the admission statement from

* `hext : ExtractV3Stmt` — soundness: `HoldsP nearAirV3` on a prepared statement
  that `prepD0` accepts yields `GoodV3` (hence, by the proved `factorSound`,
  `RelD0a`);
* `hcomp` — completeness: every `RelD0a` claim has a hint and an honest trace
  satisfying `HoldsP` with an admissible header (the `RenderV3Stmt` conclusion
  on raw witness bytes — note `prepV3b`/`Hint.encode (hintSel c w)`);
* `halign` — `AlignedV3Stmt`: the honest traces are roll-in aligned (so the
  proved size bound `nearV3_size` applies);
* `hjoin` — the proof-size framing bound (the joined `Hint.encode … ‖ π` fits
  `challengeParamsD0a.maxProofBytes`);
* `hsplits` — the `split`/`join` framing law. For the concrete codec
  `ZkFormal.NearV3.Assembly.split_join` proves it for every hint whose byte
  length fits the u32 prefix — i.e. every honest `Hint.encode` once the render
  bounds the hint; the assembly theorem states it in the (stronger, hints-only)
  form above.

`ExtractV3Stmt` (the `link` work package) and `RenderV3Stmt`/`AlignedV3Stmt`
(the `render-assembly` work package) are the remaining compiler-verified
obligations of `docs/zk-formal/STATUS-V3-ASSEMBLY.md` §3 (items 3 and 4 of the
assembly lane). Until they land the candidate is **not ADMITTED**; this theorem
is the honest, checkable reduction of the end-to-end obligation to those named
statements. It uses no `sorry`, `axiom` or `native_decide`.

The `himpl` side condition of the assembly theorem is `rfl`: for the
`nativeTrusted` route `VerifierImpl.Connection _ _ v` is `v = m`
(`formal-core/ArenaCore/Admission.lean:92`) and `Model.verifier` *is*
`(npVerifierP … split prepV3b).toVerifier` by definition.
-/

namespace NpUdrStarkV2

open ArenaCore ZkFormal ZkFormal.Air ZkFormal.Prover ZkFormal.Size ZkFormal.V2 ZkFormal.Algebra
  ZkFormal.NearV3.Assembly NearSpecV3

local instance : ZkFormal.Prover.Np.G.AuxG := ⟨2, by decide⟩

theorem certificate_of
    (hext : ExtractV3Stmt)
    (hintSel : WfClaim → List UInt8 → Hint)
    (hsplits : ∀ h π : List UInt8,
      ZkFormal.NearV3.Assembly.split (ZkFormal.NearV3.Assembly.join h π) = some (h, π))
    (traceOf : WfClaim → List UInt8 → Trace Fp)
    (hcomp : ∀ c w, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      ∃ cb', ZkFormal.NearV3.Assembly.prepV3b (WfClaim.encode c)
          (ZkFormal.NearV3.Assembly.Hint.encode (hintSel c w)) = some cb' ∧
        HoldsP nearAirV3 (Udr.pubOf Fp cb') (traceOf c w) ∧
        (ZkFormal.Prover.Np.G.VdP nearAirV3).headerOk
          (trHdr nearAirV3.toAir (traceOf c w)) = true)
    (halign : ∀ c w, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      RollAligned nearAirV3.toAir ZkFormal.Prover.Np.G.dp
        (trHdr nearAirV3.toAir (traceOf c w)))
    (hjoin : ∀ c w π, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      π.length ≤ v3MaxInner →
      (ZkFormal.NearV3.Assembly.join
        (ZkFormal.NearV3.Assembly.Hint.encode (hintSel c w)) π).length ≤
        challengeParamsD0a.maxProofBytes)
    (pd bd : Digest) (tid : String)
    (hpub : sha256 publicBin = pd) :
    AdmissionStatement challengeParamsD0a
      { publicDigest := pd, impl := .nativeTrusted bd tid Model.verifier } :=
  ZkFormal.NearV3.Assembly.nearV3_admission_with_extract_b hext
    { publicDigest := pd, impl := .nativeTrusted bd tid Model.verifier }
    publicBin hpub
    ZkFormal.NearV3.Assembly.split
    ZkFormal.NearV3.Assembly.join
    rfl
    hintSel hsplits traceOf hcomp halign hjoin

end NpUdrStarkV2
