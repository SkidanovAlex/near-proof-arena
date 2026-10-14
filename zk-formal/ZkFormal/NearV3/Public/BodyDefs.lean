import ZkFormal.NearV3.Public.PackingDefs
import ZkFormal.V2.Air

/-!
# `ZkFormal.NearV3.Public.BodyDefs`

The definitions of `ZkFormal.NearV3.Public.Body` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Public.Body` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Public

open ZkFormal.V2

def bodyPayload (body : ByteString) : Payload := (body.drop 8).map (fun b => [b])

def bodyPlan : PubSeg :=
  { bus := 0, send := false, width := 1, countAt := 0, start := 0,
    msgPrefix := [2], indexBase := some 8 }

end ZkFormal.NearV3.Public
