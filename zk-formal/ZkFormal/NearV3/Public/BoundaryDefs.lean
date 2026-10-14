import ZkFormal.NearV3.Public.PackingDefs
import ZkFormal.NearV3.Rcpt.Ids
import ZkFormal.V2.Air

/-!
# `ZkFormal.NearV3.Public.BoundaryDefs`

The definitions of `ZkFormal.NearV3.Public.Boundary` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Public.Boundary` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Public

open ZkFormal.V2

abbrev Interval := Option ByteString × Option ByteString

def boundaryRow (bounds : List Interval) (x : Nat) : ByteString :=
  let b := bounds.getD (x / BND_STRIDE) (none,none)
  let k := x % BND_STRIDE
  [(b.1.getD []).getD k 0, (b.2.getD []).getD k 0, if b.2.isNone then 1 else 0]

def boundaryPayload (bounds : List Interval) : Payload :=
  (List.range (BND_STRIDE*bounds.length)).map (boundaryRow bounds)

def boundaryPlan : PubSeg :=
  { bus := B_BNDP, send := true, width := 3, countAt := 0, start := 0, indexBase := some 0 }

end ZkFormal.NearV3.Public
