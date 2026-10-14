import ZkFormal.V2.Air

/-!
# `ZkFormal.NearV3.Public.LayoutDefs`

The definitions of `ZkFormal.NearV3.Public.Layout` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Public.Layout` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Public

open ZkFormal.V2

/-- A static segment descriptor reads its count and offset from its metadata slot. -/
def descriptor (plan : PubSeg) (headerLength i : Nat) : PubSeg :=
  { plan with countAt := headerLength+8*i, start := 0, startAt := some (headerLength+8*i+4) }

end ZkFormal.NearV3.Public
