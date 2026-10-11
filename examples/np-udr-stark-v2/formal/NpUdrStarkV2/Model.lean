import ZkFormal.NearV3.Assembly.NearAdmission
import NearSpecV3.ChallengeD0a

/-!
# The deployed verifier model `NpUdrStarkV2.Model.verifier`

`np-udr-stark-v2` for the D0a challenge `near-chunk-validation-d0-stark`
(statement `near/pv86/chunk-validation/v0#D0a`): the v2 hint verifier
`ZkFormal.Prover.Np.G.npVerifierP` at `auxGroup = 2`, compiled by BCS to the v3
AIR `ZkFormal.NearV3.Assembly.nearAirV3` (25 tables, `ZkFormal.V2.G.pg 2`),

  `npVerifierP challengeSpecD0a nearAirV3 split prepV3b`

with the deployed wire codecs of `ZkFormal.NearV3.Assembly`:

* `split` = `ZkFormal.NearV3.Assembly.split` = `readBorshBytes`
  (`Hint.encode h = u32 h.n ‖ borshBytes h.body`; `join h π = borshBytes h ‖ π`);
* `prepV3b` = `Hint.decode ⋙ prepV3` = `Hint.decode ⋙ (prepD0 ⋙ Prep.encode ⋙
  Public.preparedBytes · 0)` (`ZkFormal.NearV3.Assembly.prepV3b`), exactly what
  the Rust `prove` emits.

`npVerifierP` already includes the claim-canonicality guard
(`ZkFormal.Assembly.guardTree (claimOk challengeSpecD0a) …`, R-L7-2): the
deployed verifier rejects a non-canonical claim before any oracle query. This
definition IS the deployed model: the judge's native-lean route compiles it
(implementation-connection edge `nativeTrusted`, i.e. trusted) and the
`np-lean-verify-v2` conformance harness runs the same `npVerifierP` through
`V3.hintTree`. It is closed (no `sorry`); its import closure holds only trusted
ArenaCore/NearSpec/NearSpecV3 modules and the candidate-vendored `ZkFormal`
modules.

`auxGroup = 2` is the concrete `ZkFormal.Prover.Np.G.AuxG` instance used by
`zk-formal/ZkFormal/NearV3/Assembly/NearAdmission.lean`.
-/

namespace NpUdrStarkV2

open ArenaCore ZkFormal ZkFormal.NearV3.Assembly

/-- `auxGroup = 2` for the assembled AIR (same instance as `NearAdmission.lean`). -/
local instance : ZkFormal.Prover.Np.G.AuxG := ⟨2, by decide⟩

/-- The deployed verifier model: `npVerifierP` for D0a / `nearAirV3` with the
concrete v3 wire codecs, as an `ArenaCore.OracleVerifier`. -/
def Model.verifier : OracleVerifier :=
  (ZkFormal.Prover.Np.G.npVerifierP NearSpecV3.challengeSpecD0a
    ZkFormal.NearV3.Assembly.nearAirV3
    ZkFormal.NearV3.Assembly.split
    ZkFormal.NearV3.Assembly.prepV3b).toVerifier

end NpUdrStarkV2
