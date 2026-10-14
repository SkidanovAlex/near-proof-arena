import NearSpecV3.BandwidthScheduler

/-!
# `ZkFormal.NearV3.Sched.Spec.CanonDupDefs`

The definitions of `ZkFormal.NearV3.Sched.Spec.CanonDup` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Sched.Spec.CanonDup` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler

/-- Index of record `k`'s link under the spec's `indexOf`. -/
def tgt (ids : List Nat) (k : Nat) : Nat :=
  (indexOf ids (ids.getD (k / ids.length) 0)).getD 0 * ids.length +
    (indexOf ids (ids.getD (k % ids.length) 0)).getD 0

/-- The last record mapped to link `l`. -/
def srcOf (ids : List Nat) (l : Nat) : Option Nat :=
  ((List.range (ids.length * ids.length)).filter fun k => tgt ids k == l).getLast?

end ZkFormal.NearV3.Sched
