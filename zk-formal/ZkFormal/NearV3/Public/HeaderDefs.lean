import NearSpec.Bytes
import NearSpecV3.PrepD0
import ZkFormal.NearV3.Public.PackingDefs

/-!
# `ZkFormal.NearV3.Public.HeaderDefs`

The definitions of `ZkFormal.NearV3.Public.Header` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Public.Header` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Public

open NearSpec NearSpecV3

/-- Preserve the existing static AIR offsets, and add body length and witness overhead. -/
def headerBytes (p : Prep) (witnessOverhead : Nat) : ByteString :=
  borshBytes prepTag ++ p.hdr.encode ++ u32 p.body.length ++ u32 witnessOverhead

end ZkFormal.NearV3.Public
