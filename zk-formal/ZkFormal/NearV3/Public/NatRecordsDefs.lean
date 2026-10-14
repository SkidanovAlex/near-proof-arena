import ZkFormal.NearV3.Public.PackingDefs

/-!
# `ZkFormal.NearV3.Public.NatRecordsDefs`

The definitions of `ZkFormal.NearV3.Public.NatRecords` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Public.NatRecords` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Public


def natPayload (records : List (List Nat)) : Payload := records.map (·.map UInt8.ofNat)

end ZkFormal.NearV3.Public
