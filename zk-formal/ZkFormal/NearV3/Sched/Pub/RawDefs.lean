import NearSpecV3.PrepD0
import ZkFormal.NearV3.Sched.ModelDefs
import ZkFormal.NearV3.Sched.RenderDefs
import ZkFormal.NearV3.Sched.Spec.ConvDefs

/-!
# `ZkFormal.NearV3.Sched.Pub.RawDefs`

The definitions of `ZkFormal.NearV3.Sched.Pub.Raw` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Sched.Pub.Raw` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler NearSpec

/-- The AIR's public instance record of the scheduler public data `sp`. -/
def instOf (sp : SchedPub) : InstPub :=
  ⟨sp.ids, sp.params, sp.allowed,
    (rawOf sp.ids sp.raw).filter (fun q => !(incsOf sp.params q.bm).isEmpty),
    sp.seed, sp.allShardsHash⟩

end ZkFormal.NearV3.Sched
