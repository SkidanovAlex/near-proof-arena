import ZkFormal.NearV3.D1.VerifierD1Defs
import NearSpecV3.ChallengeChunkV3

/-!
# `ZkFormal.NearV3.D1.ModelTier` — the D1a verifier model against the tier spec (item A3)

Lane `v3-d1-phase2` (docs/zk-formal/V3-D1-PHASE2.md §1).  The judge's expected type for
`near-chunk-v3` at `Tier.d1a` is `AdmissionStatement (challengeParamsChunkWith .d1a …)`, i.e.
`challengeParamsChunk .d1a` at the frozen literals, whose spec is `challengeSpecChunk .d1a`.  The
phase-1 model (`VerifierD1Defs`) is stated with `challengeSpecD1a`; `npVerifierP` reads the spec
only through `claimOk` (`decodeClaim`), so the two verifiers are the same term, and the tier's
fuel / profile / proof cap / reduction fuel are `challengeParamsD1a`'s.  The specs differ only in
`Domain` (the tier's adds `|w| ≤ 64 MiB`), which only the completeness side reads.
-/

namespace ZkFormal.NearV3.D1

open NearSpecV3 ZkFormal.NearV3.Assembly

/-- The deployed auxiliary-group parameter `g = 2`. -/
local instance auxG2_modelTier : ZkFormal.Prover.Np.G.AuxG := ⟨2, by decide⟩

theorem verifierD1_tier :
    ZkFormal.Prover.Np.G.npVerifierP challengeSpecD1a nearAirV3D1 split prepD1b =
      ZkFormal.Prover.Np.G.npVerifierP (challengeSpecChunk .d1a) nearAirV3D1 split prepD1b := by
  unfold ZkFormal.Prover.Np.G.npVerifierP
  have : ZkFormal.Assembly.claimOk challengeSpecD1a = ZkFormal.Assembly.claimOk (challengeSpecChunk .d1a) := by
    funext cb; simp only [ZkFormal.Assembly.claimOk, challengeSpecD1a, challengeSpecChunk]
    cases WfClaim.decode cb <;> rfl
  rw [this]

theorem paramsD1a_tier :
    (challengeParamsChunk .d1a).verifyFuel = challengeParamsD1a.verifyFuel ∧
    (challengeParamsChunk .d1a).profile = challengeParamsD1a.profile ∧
    (challengeParamsChunk .d1a).maxProofBytes = challengeParamsD1a.maxProofBytes ∧
    (challengeParamsChunk .d1a).maxReductionFuel = challengeParamsD1a.maxReductionFuel :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The tier's relation is `RelD1a B0` on the encoded claim (the soundness target). -/
theorem relTier_d1a (c : WfClaim) (w : List UInt8) :
    (challengeSpecChunk .d1a).Rel c w ↔ RelD1a B0 c.1.encode w := Iff.rfl

end ZkFormal.NearV3.D1
