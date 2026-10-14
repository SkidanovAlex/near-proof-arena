import NearSpecV3.ChallengeD1
import NearSpecV3.ChunkValidationD1a

/-!
# `ArenaCore.ChallengeSpec` instance for domain D1a (`RelD1a`)

The bounded D1 relation (spec/near-chunk-validation-d1a.md): same claim type, codec and witness
format as the D0 / D1 instances; `Rel c w = RelD1a B0 c.encode w`
(`RelD1 ∧ A1 ∧ A2 ∧ Canon0f ∧ A7 B0 ∧ A8 ∧ A9 W0 ∧ A10 Dp0 ∧ A12 ∧ T1 NT0`, each D0a amendment
restated over the D1 witness and run; a pure restriction of D1, `relD1a_relD1`).

No challenge uses this instance yet; it is the standalone analogue of `challengeParamsD0a`, and
the tier `NearSpecV3.challengeParamsChunk .d1a` of `near-chunk-v3` is the coverage-tiered one.
The formal proof-size cap is `maxProofBytesV3` = 64 MiB (user decision P-D1-5, 2026-10-14: no
extra bound; T2 `|new_transactions| ≤ NT` is therefore not part of D1a).
-/

namespace NearSpecV3

open ArenaCore

def WfClaim.RelD1a (c : WfClaim) (w : List UInt8) : Prop := NearSpecV3.RelD1a B0 c.1.encode w
def WfClaim.DomainD1a (c : WfClaim) : Prop := ∃ w, WfClaim.RelD1a c w

/-- Claim-level lift: a D1a statement is a D1 statement. -/
theorem WfClaim.relD1a_rel {c : WfClaim} {w : List UInt8} (h : WfClaim.RelD1a c w) :
    WfClaim.RelD1 c w := relD1a_relD1 h

theorem WfClaim.domainD1a_domain {c : WfClaim} (h : WfClaim.DomainD1a c) : WfClaim.DomainD1 c :=
  let ⟨w, hw⟩ := h; ⟨w, WfClaim.relD1a_rel hw⟩

def challengeSpecD1a : ChallengeSpec where
  Claim := WfClaim
  Witness := List UInt8
  Rel := WfClaim.RelD1a
  Domain := WfClaim.DomainD1a
  decodeClaim := WfClaim.decode
  encodeClaim := WfClaim.encode
  decode_encode := WfClaim.decode_encode

def challengeParamsD1a : ChallengeParams where
  spec := challengeSpecD1a
  profile := NearSpec.TransferV1.profileValidityClassical128
  verifyFuel := verifyFuelV3
  maxProofBytes := maxProofBytesV3
  maxReductionFuel := maxReductionFuelV3

end NearSpecV3
