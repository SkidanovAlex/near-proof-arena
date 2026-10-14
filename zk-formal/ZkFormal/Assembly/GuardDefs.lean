import ArenaCore.Bytes
import ArenaCore.Relation
import ArenaCore.Security.OracleComp
import ArenaCore.Security.ROMLemmas
import ZkFormal.GameDefs

/-!
# `ZkFormal.Assembly.GuardDefs`

The definitions of `ZkFormal.Assembly.Guard` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.Assembly.Guard` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.Assembly

open ArenaCore ArenaCore.Security ZkFormal

/-- Reject claims failing `ok` before running `V`. -/
def guardTree (ok : Bytes → Bool) (V : TreeVerifier) : TreeVerifier :=
  ⟨fun pub cb pb => if ok cb then V.tree pub cb pb else .pure false⟩

/-- Canonical claim bytes of a challenge: they decode, and re-encode to themselves. -/
def claimOk (S : ChallengeSpec) (cb : Bytes) : Bool :=
  match S.decodeClaim cb with
  | some c => S.encodeClaim c == cb
  | none => false

end ZkFormal.Assembly
