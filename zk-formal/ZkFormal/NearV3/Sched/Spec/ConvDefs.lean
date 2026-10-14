import NearSpecV3.BandwidthScheduler
import ZkFormal.NearV3.Sched.ModelDefs

/-!
# `ZkFormal.NearV3.Sched.Spec.ConvDefs`

The definitions of `ZkFormal.NearV3.Sched.Spec.Conv` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Sched.Spec.Conv` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler NearSpec

/-- Raw requests with resolved shard indices, in the spec's order (unknown shards dropped). -/
def rawOf (ids : List Nat) (rs : List (Nat × List BandwidthRequest)) : List RawReq :=
  rs.flatMap fun (sender, brs) => brs.filterMap fun br =>
    match indexOf ids sender, indexOf ids br.toShard with
    | some s, some r => some ⟨s, r, br.bitmap⟩
    | _, _ => none

end ZkFormal.NearV3.Sched
