import ZkFormal.NearV3.Assembly.LinkShape
import ZkFormal.NearV3.Assembly.LinkSource
import ZkFormal.NearV3.Assembly.A7SegMatch
import ZkFormal.NearV3.Assembly.RenderV3Bundle

/-!
# ZkFormal.NearV3.Assembly.ExtractV3Proof — the soundness obligation `ExtractV3Stmt`, proved

`ExtractV3Stmt ⇐ LinkV3Stmt B0 ⇐ LinkCoreV3Stmt B0 ⇐ LinkRestV3Stmt B0 ⇐ LinkRest2V3Stmt B0`
(`extractV3_of_link`, `linkV3_of_core`, `linkCore_of_rest`, `linkRest_of_rest2`).  The last link,
for the reconstruction `xOf r (dictOf p r)`:

* `shape` — `LinkShape.shape_xOf`;
* `witnessBytes` — `LinkWitness.witnessBytes_xOf` (a capacity consequence of `HoldsP`);
* `canonicalScheduler` — `LinkCanon.canonicalScheduler_xOf`;
* `unfoldedBytes` (A7) — `A7Match.unfoldedBytes_holds` (lane A);
* `chachaWords` (A9) — `A9Native.chachaWords_xOf` (lane A);

the last three with `shape` and `source.applied` (`source_of_records`).

**`linkRest2_B0 : LinkRest2V3Stmt B0`** and **`extractV3 : ExtractV3Stmt`** (unconditional), hence
**`nearV3_admission_of_complete`**: the admission certificate from the completeness obligation
`CompleteV3Stmt` alone.
-/

namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpecV3

/-- The deployed auxiliary-group parameter `g = 2` (as `NearAdmission` / `RenderV3Bundle`). -/
local instance : ZkFormal.Prover.Np.G.AuxG := ⟨2, by decide⟩

/-- **The remaining link fields at `B0`.** -/
theorem linkRest2_B0 : LinkRest2V3Stmt NearSpecV3.B0 := by
  intro cb h p oh tr r k hp hw C hsz hH W T _ _ _
  have hs := LinkShape.shape_xOf hp hw C hsz hH W T
  have happ := (source_of_records hp hsz hH T W hw).applied
  exact ⟨hs, LinkWitness.witnessBytes_xOf hp hw C hsz hH W T,
    LinkCanon.canonicalScheduler_xOf hp hw hsz hH W T _ hs happ,
    A7Match.unfoldedBytes_holds hp hw hsz hH W T _ hs happ,
    A9Native.chachaWords_xOf hp hw hsz hH W T _ hs happ⟩

/-- **The soundness obligation of the D0a certificate, proved.** -/
theorem extractV3 : ExtractV3Stmt :=
  extractV3_of_link (linkV3_of_core (linkCore_of_rest (linkRest_of_rest2 linkRest2_B0)))

/-- **The v3 admission certificate from completeness alone** (`nearV3_admission_of` with
`extractV3`). -/
theorem nearV3_admission_of_complete (hc : CompleteV3Stmt)
    (art : ArenaCore.ArtifactDescription) (pub : List UInt8) (hpub : sha256 pub = art.publicDigest)
    (himpl : art.impl.Connection challengeParamsD0a.verifyFuel
      (ZkFormal.Prover.Np.G.npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier) :
    ArenaCore.AdmissionStatement challengeParamsD0a art :=
  nearV3_admission_of extractV3 hc art pub hpub himpl

end ZkFormal.NearV3.Assembly
