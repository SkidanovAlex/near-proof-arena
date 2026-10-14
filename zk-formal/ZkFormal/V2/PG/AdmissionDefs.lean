import ArenaCore.Bytes
import ArenaCore.Relation
import ZkFormal.Algebra.Fp
import ZkFormal.Algebra.Fp8
import ZkFormal.Assembly.GuardDefs
import ZkFormal.GameDefs
import ZkFormal.Stark.InstanceDefs
import ZkFormal.V2.Air
import ZkFormal.V2.PG.NpDefsCore
import ZkFormal.V2.VerifierDefs
import ZkFormal.V3.HintDefs

/-!
# `ZkFormal.V2.PG.AdmissionDefs`

The definitions of `ZkFormal.V2.PG.Admission` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.V2.PG.Admission` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
  ZkFormal.Prover ZkFormal.Assembly ZkFormal.V2

/-- **The deployed v2 verifier with hints**: claim guard, hint split, native
preprocessing, then the compiled v2 STARK verifier on the prepared statement. -/
def npVerifierP (S : ChallengeSpec) (AP : AirP) (split : Bytes → Option (Bytes × Bytes))
    (prep : Bytes → Bytes → Option Bytes) : TreeVerifier :=
  guardTree (claimOk S) (V3.hintTree split prep (verifierP Fp Fp8 AP dp))

end ZkFormal.Prover.Np.G

namespace ZkFormal.V2.G

open ArenaCore ArenaCore.Security ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra ZkFormal.Prover
  ZkFormal.Assembly

end ZkFormal.V2.G
