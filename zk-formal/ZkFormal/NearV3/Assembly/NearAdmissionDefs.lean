import NearSpecV3.PrepD0
import ZkFormal.Algebra.Fp
import ZkFormal.NearV3.Assembly.HintCodec
import ZkFormal.NearV3.Public.PreparedDefs

/-!
# `ZkFormal.NearV3.Assembly.NearAdmissionDefs`

The definitions of `ZkFormal.NearV3.Assembly.NearAdmission` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Assembly.NearAdmission` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Assembly

open ArenaCore Lean.Grind ZkFormal ZkFormal.Air
  ZkFormal.Algebra ZkFormal.V2 NearSpecV3

set_option maxHeartbeats 4000000

set_option maxRecDepth 8192

/-- The canonical prepared-statement codec: `prepD0` then the protocol packing
`Public.preparedBytes` (the concrete `nearAirV3.pubSegs` public vector).  Packed
statements of `P` or more bytes are rejected (decidable, checked natively): above
that the packed `u32` totals alias in the field (see `ExtractV3StmtAt`). -/
def prepV3 (cb : List UInt8) (h : NearSpecV3.Hint) : Option (List UInt8) :=
  match NearSpecV3.prepD0 cb h with
  | .ok p =>
    if (ZkFormal.NearV3.Public.preparedBytes p 0).length < ZkFormal.Algebra.P then
      some (ZkFormal.NearV3.Public.preparedBytes p 0)
    else none
  | .error _ => none

/-- The canonical prepared-statement codec on raw witness bytes: decode the clear
hint, then `prepD0 ∘ Prep.encode`. -/
def prepV3b (cb : List UInt8) (hb : List UInt8) : Option (List UInt8) :=
  (ZkFormal.NearV3.Assembly.Hint.decode hb).bind (prepV3 cb)

end ZkFormal.NearV3.Assembly
